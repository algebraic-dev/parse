import Lean.Elab.Command

/-!
  Data types for describing a grammar in the Parse library.
-/

open Lean

namespace Parse.HS

inductive Invoker
  | callback (prop: Name) (to: Name)
  | start (prop: Name) (to: Name)
  | close (prop: Name) (to: Name)
  | store (prop: Name) (to: Name)
  | error (num: Nat)
  | goto (to: Name)
  deriving Repr

inductive Matcher
  | switch (cases: Array (String × Syntax)) (inv: Invoker)
  | is (prop: String) (inv: Invoker)
  | peek (prop: Char) (inv: Invoker)
  | otherwise (inv: Invoker)
  | goto (inv: Invoker)
  deriving Repr

structure Node where
  name : Name
  matchers : Array Matcher
  deriving Repr

structure Property where
  name : Name
  value : Syntax
  deriving Repr

structure Grammar where
  name : Name
  nodes : Array Node
  props : Array Property

def Invoker.getName : Invoker → Option Name
  | callback _ inv => some inv
  | start _ inv => some inv
  | close _ inv => some inv
  | store _ inv => some inv
  | goto inv => some inv
  | error _ => none

def Matcher.getName : Matcher → Option Name
  | .switch _ inv => inv.getName
  | .is _ inv => inv.getName
  | .peek _ inv => inv.getName
  | .otherwise inv => inv.getName
  | .goto inv => inv.getName

end HS

namespace LS

inductive Instruction
  | when (branches: Array (Char × Array Instruction))
  | check (s: String) (inv: Array Instruction)
  | callback (prop: Name)
  | start (prop: Name)
  | close (prop: Name)
  | store (prop: Name) (data: Syntax)
  | error (num: Nat)
  | goto (to: Nat)
  | next (more: Nat)
  deriving Repr, Inhabited

structure Grammar where
  start : Name
  map   : HashMap Name Nat
  calls : HashSet Name
  props : Array (Name × Syntax)
  names : Array (Option Name)
  nodes : Array (Array Instruction)
  deriving Inhabited

def Grammar.new (start: Name) : Grammar :=
  let default : Grammar := Inhabited.default
  { default with start := start }

structure Case where
  idx : Nat
  string : String
  capture: Bool
  inv: HS.Invoker
  data: Option Syntax
  deriving Repr

def Case.fromMatcher (idx: Nat) : HS.Matcher → Array Case
  | .switch cases inv =>
    cases.map (λ⟨string, data⟩ => {idx, string, capture := true, inv, data := some data})
  | .is string inv =>
    #[{idx, string, capture := true, inv, data := none}]
  | .peek char inv =>
    #[{idx, string := char.toString, capture := false, inv, data := none}]
  | .goto inv =>
    #[{idx, string := "", capture := false, inv, data := none}]
  | .otherwise inv =>
    #[{idx, string := "", capture := true, inv, data := none}]

def Case.isEmpty (case: Case) : Bool :=
  case.string.isEmpty

def Case.prefix? (case: Case) : Option Char :=
  if case.string.isEmpty
    then none
    else some case.string.front

def Case.next (case: Case) : Case :=
  if case.isEmpty
    then case
    else { case with string := case.string.drop 1 }

def Case.specialize (char: Char) (case: Case) : Option Case :=
  match case.prefix? with
  | none => some case
  | some pfx =>
    if pfx == char
      then some case.next
      else none

def Grammar.getName (grammar: Grammar) (name: Name) : Nat :=
  grammar.map.findD name 0

def Grammar.addName (grammar: Grammar) (name: Name) : Grammar :=
  if Option.isSome $ grammar.map.find? name
    then grammar
    else { grammar with map := grammar.map.insert name grammar.names.size,
                        names := grammar.names.push (some name),
                        nodes := grammar.nodes.push #[] }

def Grammar.addCallback (grammar: Grammar) (name: Name) : Grammar :=
  { grammar with calls := grammar.calls.insert name }

def Invoker.compile (grammar: Grammar) (data: Option Syntax) (code: Array Instruction) : HS.Invoker → Array Instruction
  | .callback name to =>
    (code.push (Instruction.callback name)).push (Instruction.goto (grammar.getName to))
  | .start prop to =>
    (code.push (Instruction.start prop)).push (Instruction.goto (grammar.getName to))
  | .close prop to =>
    (code.push (Instruction.close prop)).push (Instruction.goto (grammar.getName to))
  | .store prop to =>
    match data with
    | some data => (code.push (Instruction.store prop data)).push (Instruction.goto (grammar.getName to))
    | none => code.push (Instruction.goto (grammar.getName to))
  | .error data => code.push (Instruction.error data)
  | .goto to =>  code.push (Instruction.goto (grammar.getName to))

def Invoker.registerName (grammar: Grammar) : HS.Invoker → Grammar
  | .callback node to => (grammar.addName to).addCallback node
  | .start _ to => grammar.addName to
  | .close _ to => grammar.addName to
  | .store _ to => grammar.addName to
  | .error _ => grammar
  | .goto to => grammar.addName to

abbrev CompileM := StateM (Grammar × Array String)

def CompileM.addName (name: Name) : CompileM Unit :=
  StateT.modifyGet (λ(grammar, errors) => ((), (grammar.addName name, errors)))

def CompileM.getGrammar : CompileM Grammar :=
  Prod.fst <$> StateT.get

def CompileM.getName (name: Name) : CompileM Nat :=
  (Grammar.getName · name) <$> CompileM.getGrammar

def CompileM.setCode (place: Nat) (code: Array Instruction) : CompileM Unit :=
  StateT.modifyGet (λ(grammar, errors) => ((), ({ grammar with nodes := grammar.nodes.set! place code }, errors)))

def CompileM.addError (err: String) : CompileM Unit :=
  StateT.modifyGet (λ(grammar, errors) => ((), (grammar, errors.push err)))

def Case.registerName (grammar: Grammar) (case: Case) : Grammar :=
  Invoker.registerName grammar case.inv

def Case.compile (num: Nat) (grammar: Grammar) (instructions: Array Instruction) (case: Case) : Array Instruction := Id.run $ do
  let mut instructions := instructions

  if case.capture
    then instructions := instructions.push (Instruction.next num)

  instructions := Invoker.compile grammar case.data instructions case.inv

  return instructions

abbrev Problem := Array Case

def Problem.fromMatchers (matchers: Array HS.Matcher) : Array Case :=
  let enumerated := matchers.mapIdx ((·.val, ·))
  enumerated.concatMap (λ(idx, data) => Case.fromMatcher idx data)

def Problem.trim (array: Array Case) : Array Case :=
  let idx := array.findIdx? (λx => x.string.isEmpty)
  match idx with
  | none     => array.push ({string := "", idx := 0, capture := false, inv := HS.Invoker.error 1, data := none})
  | some idx => array.extract 0 (idx + 1)

def Problem.specializeFor (prefix_: Char) (problem: Problem) : Problem :=
  problem.filterMap (Case.specialize prefix_)

def Problem.isConcluded (problem: Problem) : Option Case := do
  let case ← problem.get? 0
  if case.isEmpty
    then some case
    else none

def Problem.willMatch (prefix_: Char) (problem: Problem) : Bool :=
  Option.isSome (problem.find? (·.string == prefix_.toString))

instance : Hashable Char where
  hash x := x.val.toUInt64

def Problem.prefixes (problem: Problem) : HashSet Char :=
  (problem.filterMap Case.prefix?).foldl HashSet.insert Inhabited.default

def Problem.getAlt (problem: Problem) : Option Case :=
  problem.find? Case.isEmpty

partial def Problem.accumulate (problem: Problem) (s: String) : (Problem × String) :=
  let prefixes := problem.prefixes.toArray
  if prefixes.size == 1
    then let prefix_ := prefixes.get! 0
         if Problem.willMatch prefix_ problem
          then (problem.specializeFor prefix_, s.push prefix_)
          else Problem.accumulate (problem.specializeFor prefix_) (s.push prefix_)
    else (problem, s)

partial def Problem.specialize (code: Array Instruction) (num: Nat) (problem: Problem) : CompileM (Array Instruction) := do
  let grammar ← CompileM.getGrammar
  if problem.isEmpty then pure #[Instruction.error 0] else
  match problem.isConcluded with
  | some case =>
    pure (case.compile num grammar #[])
  | none => do
    let (problem₂, str) := problem.accumulate ""
    if str.isEmpty then
      let prefixes := problem₂.prefixes.toArray
      let subProblems ← prefixes.mapM $ λprefix_ => do
        let bind ← Problem.specializeFor prefix_ problem₂
                 |> Problem.specialize #[Instruction.next 1] 1
        pure (prefix_, bind)

      let mut code := code
      code := code.push (Instruction.when subProblems)

      match problem₂.getAlt with
      | some case => pure $ case.compile num grammar code
      | none => pure code
    else
      let res ← Problem.specialize #[Instruction.next str.length] (str.length) problem₂
      let code :=
        if str.length == 1
          then code.push (Instruction.when #[(str.front, res)])
          else code.push (Instruction.check str res)
      match problem.getAlt with
      | some case => pure $ case.compile num grammar code
      | none => pure code

def Grammar.registerNode (node: HS.Node) : CompileM Unit := do
  CompileM.addName node.name
  for matcher in node.matchers do
    match matcher.getName with
    | none     => pure ()
    | some res => CompileM.addName res

def Grammar.compile' (nodes: Array HS.Node) : CompileM Unit := do
  for node in nodes do Grammar.registerNode node

  for node in nodes do
    let place ← CompileM.getName node.name
    let code ← Problem.specialize #[] 1 (Problem.fromMatchers node.matchers |> Problem.trim)
    CompileM.setCode place code

def Instruction.needsSplit : Instruction → Bool
  | .when _ => true
  | .check _ _ => true
  | _ => false

def breakOn (array: Array α) (p: α → Bool) : (Array α × Array α) := Id.run do
  let mut arr₁ := #[]
  let mut arr₂ := #[]
  let mut cond := false

  for elem in array do
    if p elem then
      cond := true

    if cond
      then arr₂ := arr₂.push elem
      else arr₁ := arr₁.push elem

  return (arr₁, arr₂)

def Grammar.addNewCode (grammar: Grammar) (code: Array Instruction) : (Grammar × Nat) :=
  let size := grammar.names.size
  let grammar := {grammar with names := grammar.names.push none, nodes := grammar.nodes.push code }
  (grammar, size)

def Grammar.codeHasBranch (code: Array Instruction) : (Array Instruction × Array Instruction) :=
  breakOn code Instruction.needsSplit

mutual
  partial def Grammar.splitCode (grammar: Grammar) (code: Array Instruction) : (Grammar × Array Instruction) :=
    code.foldl (λ(grammar, insts) current_inst =>
                    let (grammar, inst) := Grammar.splitOnInstruction grammar current_inst
                    (grammar, insts.push inst)
                  ) (grammar, #[])

  partial def Grammar.splitOnInstruction (grammar: Grammar) : Instruction → (Grammar × Instruction)
    | .when alts => Id.run do
      let mut alts₂ := #[]
      let mut grammar := grammar
      for (p, code) in alts do
        let (grammar₂, code₂) := Grammar.splitCode grammar code
        grammar := grammar₂

        let mut code₂ := code₂

        let (stt, end_) := Grammar.codeHasBranch code₂

        if !end_.isEmpty
          then do
            let (grammar₂, place) := grammar.addNewCode end_
            code₂ := stt.push (Instruction.goto place)
            grammar := grammar₂

        alts₂ := alts₂.push (p, code₂)
      (grammar, .when alts₂)
    | .check str code =>
      let (grammar, splitted) := Grammar.splitCode grammar code

      let (stt, end_) := Grammar.codeHasBranch splitted

      if !end_.isEmpty
        then let (grammar, place) := grammar.addNewCode end_
             let stt := stt.push (Instruction.goto place)
             (grammar, .check str stt)
        else (grammar, .check str stt)
    | inst => (grammar, inst)
end

def Grammar.split (grammar: Grammar) : Grammar := Id.run do
  let mut grammar := grammar

  for (nat, code) in grammar.nodes.mapIdx ((·, ·)) do
    let mut code₂ := #[]
    for inst in code do
      let (grammar₂, inst₂) := Grammar.splitOnInstruction grammar inst
      grammar := grammar₂
      code₂ := code₂.push inst₂
    grammar := { grammar with nodes := grammar.nodes.set! nat code₂ }

  grammar

def Grammar.compile (grammar₀: HS.Grammar) : Except (Array String) Grammar :=
  let grammar := Grammar.new grammar₀.name
  let grammar := {grammar with props := grammar₀.props.map (λp => (p.name, p.value))}
  let (grammar, errors) := Prod.snd $ Id.run $ StateT.run (Grammar.compile' grammar₀.nodes) (grammar, #[])
  if errors.isEmpty
    then Except.ok grammar
    else Except.error errors

-- Pretty printing

def Array.joinMap (f: α → String) := Array.foldl String.append "" ∘ Array.map f

inductive RoseTree where
  | node (label : String) (children : Array RoseTree)
  deriving Inhabited

mutual
  partial def Nodes.toStr (prefix_: String) (array: Array Instruction) : RoseTree :=
    RoseTree.node s!"{prefix_}: " (array.map Node.toStr )

  partial def Node.toStr : Instruction → RoseTree
    | .when alts => RoseTree.node ".when" (alts.map (λ(x, y) => Nodes.toStr x.toString y))
    | .check x code => RoseTree.node ".check" #[(Nodes.toStr x code)]
    | .callback x => RoseTree.node s!".callback {x} " #[]
    | .start x => RoseTree.node s!".start {x} " #[]
    | .close x => RoseTree.node s!".close {x} " #[]
    | .store x y => RoseTree.node s!".store {x} {y}" #[]
    | .error y => RoseTree.node s!".error {y}" #[]
    | .goto x => RoseTree.node s!".goto {x} " #[]
    | .next i => RoseTree.node s!".next {i}" #[]
end

partial def RoseTree.toString (ident: String) : RoseTree → String
  | .node label child =>
    s!"{ident}{label}\n" ++ Array.joinMap (RoseTree.toString s!"  {ident}") child

def Grammar.toStr (grammar: Grammar) : String :=
  RoseTree.toString "" (RoseTree.node "grammar: " (grammar.nodes.mapIdx (λi p => Nodes.toStr s!"({i}) {grammar.names.get! i}" p)))
