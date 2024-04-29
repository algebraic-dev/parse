import Parse.Compile.Syntax
import Parse.Compile.Tree
import Lean.Data

/-!
  Module for the specialization of the syntax into a [Instruction] tree
-/

open Parse.Syntax Parse.Tree Lean

namespace Parse.Specialize

scoped instance : Hashable Char where
  hash x := x.val.toUInt64

structure Case where
  place : Lean.Syntax
  string : String
  capture : Bool
  created : Bool
  inv : Invoker
  data : Option Lean.Syntax
  deriving Inhabited, Repr

def Case.isEmpty (case: Case) : Bool :=
  case.string.isEmpty

def Case.prefix? (case: Case) : Option Char :=
  if case.string.isEmpty
    then none
    else some case.string.front

def Case.next (case: Case) : Case :=
  if case.isEmpty
    then {case with created := false }
    else { case with string := case.string.drop 1 }

def Case.specialize (char: Char) (case: Case) : Option Case :=
  match case.prefix? with
  | none => some case.next
  | some pfx =>
    if pfx == char
      then some case.next
      else none

def Case.fromMatcher : Matcher → Array Case
  -- Need to make some optimization in order to run it faster.
  | .select _ alts inv =>
    alts.map (λ⟨place, string⟩ => {place, string := string.toString, created := true, capture := true, inv, data := none})
  | .switch _ cases inv =>
    cases.map (λ⟨place, string, data⟩ => {place, string, created := true, capture := true, inv, data := some data})
  | .is place string inv =>
    #[{place, string, created := true,capture := true, inv, data := none}]
  | .peek place char inv =>
    #[{place, created := true, string := char.toString, capture := false, inv, data := none}]
  | .goto place inv =>
    #[{place, created := false, string := "", capture := false, inv, data := none}]
  | .otherwise place inv =>
    #[{place, created := false, string := "", capture := true, inv, data := none}]

abbrev CompileM := StateM (Machine × Array (Lean.Syntax × String))

def CompileM.setMachine (f: Machine → Machine) : CompileM PUnit :=
  StateT.modifyGet (λpair => ((), (f pair.fst, pair.snd)))

def CompileM.getMachine : CompileM Machine :=
  Prod.fst <$> StateT.get

def CompileM.modifyMachine (f: Machine → (Machine × α)) : CompileM α :=
  StateT.modifyGet (λpair => let res := f pair.fst; (res.snd, (res.fst, pair.snd)))

def CompileM.addError (err: Lean.Syntax × String) : CompileM PUnit :=
  StateT.modifyGet (λpair => ((), (pair.fst, pair.snd.push err)))

def CompileM.registerName (name: Tag) : CompileM Nat :=
  CompileM.modifyMachine (Machine.createNamedNode · name)

def CompileM.registerAnonName : CompileM Nat :=
  CompileM.modifyMachine Machine.createNode

def CompileM.setCode (idx: Nat) (code: Instruction) : CompileM PUnit :=
  CompileM.setMachine (Machine.setCode · idx code)

def CompileM.nodeSize : CompileM Nat := do
  let machine ← getMachine
  return machine.nodes.size

def CompileM.getCode (idx: Nat) : CompileM Instruction := do
  let machine ← getMachine
  return machine.nodes.get! idx

def CompileM.getNameIndex (name: Name) : CompileM Nat :=
  modifyMachine (λmachine => (machine, machine.mapper.find! name))

abbrev Problem := Array Case

def Problem.fromMatchers (matchers: Array Matcher) : Problem :=
  matchers.concatMap Case.fromMatcher

def Problem.trim (problem: Problem) : Problem :=
  if let some idx := problem.findIdx? (·.string.isEmpty)
    then problem.extract 0 (idx + 1)
    else problem

def Problem.filterByPrefix (problem: Problem) (prefix_: Char) : Problem :=
  problem.filterMap (Case.specialize prefix_)

def Problem.getFirstDone (problem: Problem) : Option Case := do
  let case ← problem.get? 0
  if case.isEmpty
    then some case
    else none

def Problem.completed (problem: Problem) : Bool :=
  problem.getFirstDone.isSome

def Problem.willMatch (prefix_: Char) (problem: Problem) : Bool :=
  Option.isSome (problem.find? (·.string == prefix_.toString))

def Problem.prefixes (problem: Problem) : HashSet Char :=
  (problem.filterMap Case.prefix?).foldl HashSet.insert Inhabited.default

def Problem.getDone (problem: Problem) : Option Case :=
  problem.find? Case.isEmpty

def Problem.removeRedundant (problem: Problem) : CompileM Unit := do
  let mut problem := problem

  for idx in [1:problem.size] do
    let case := problem[idx]!
    if case.created then
      CompileM.addError (case.place, "redundant alternative")

def Invoker.compile (data: Option Lean.Syntax) : Invoker → CompileM Instruction
  | .callback func to => do
    let idx ← CompileM.getNameIndex to.getId
    return Instruction.call func idx
  | .start prop to => do
    let idx ← CompileM.getNameIndex to.getId
    return Instruction.start prop (Instruction.goto idx)
  | .close prop to => do
    let idx ← CompileM.getNameIndex to.getId
    return Instruction.close prop (Instruction.goto idx)
  | .store method to => do
    let idx ← CompileM.getNameIndex to.getId
    return if let some data := data
      then Instruction.store method data (Instruction.goto idx)
      else Instruction.goto idx
  | .goto to => do
    let idx ← CompileM.getNameIndex to.getId
    return Instruction.goto idx
  | .error num =>
    return Instruction.error num

def Case.compile (matched: Nat) (case: Case) : CompileM Instruction := do
  let result ← Invoker.compile case.data case.inv
  return if case.capture
    then Instruction.next matched result
    else result

def Problem.getNextCase (matched : Nat) (problem : Problem) : CompileM Instruction :=
  match problem.find? Case.isEmpty with
  | none      => return Instruction.failed
  | some case => case.compile matched

partial def Problem.accumulate (acc: String) (problem: Problem) : Problem × String :=
  let prefixes := problem.prefixes.toArray
  if prefixes.size != 1
    then (problem, acc)
    else let prefix_ := prefixes.get! 0
         if problem.willMatch prefix_
          then (problem.filterByPrefix prefix_, acc.push prefix_)
          else Problem.accumulate (acc.push prefix_) (problem.filterByPrefix prefix_)

partial def Problem.specialize (matched: Nat) (problem: Problem) : CompileM Instruction :=
  if problem.isEmpty then return Instruction.failed else
  if let some case := problem.getFirstDone
    then do
         problem.removeRedundant
         case.compile matched
    else do
         let else_ ← problem.getNextCase 1
         let (problem, used) := problem.accumulate ""
         let prefixes := problem.prefixes.toArray
         match used.length with
         | 0 => do
           let filtered := prefixes.map (λp => (p, Problem.filterByPrefix problem p))
           let subProblems ← filtered.mapM $ λ(pre, p) => do
             let instruction ← Problem.specialize 1 p
             if p.completed
               then return (pre, instruction)
               else return (pre, Instruction.next 1 instruction)
           return Instruction.when subProblems else_
         | 1 => do
           let chr := used.front
           let then_ ← problem.specialize used.length
           let then_ := if problem.completed then then_ else Instruction.next 1 then_
           return Instruction.when #[(chr, then_)] else_
         | _ => do
           let then_ ← problem.specialize used.length
           let then_ := if problem.completed then then_ else Instruction.next used.length then_
           return Instruction.check used then_ else_

def specialize' (grammar: Grammar) : CompileM Unit := do
  for (_, node) in grammar.nodes.toArray do
      let _ ← CompileM.registerName node.name

  for (_, node) in grammar.nodes.toArray do
    for (_, tags) in node.nodeNames.toArray do
      let _ ← CompileM.registerName tags[0]!

  for (name, node) in grammar.nodes.toArray do
    let idx ← CompileM.getNameIndex name
    let problem := Problem.fromMatchers node.matchers
    let code ← Problem.specialize 1 problem
    CompileM.setMachine (Machine.setCode · idx code)

def registerNewCode (inst: Instruction) (name: Option Tag := none) : CompileM Nat := do
  match inst with
  | .goto to => return to
  | _ => do
    let idx ←
      match name with
      | some res => CompileM.registerName res
      | none => CompileM.registerAnonName
    CompileM.setCode idx inst
    return idx

partial def splitInstruction' : Instruction → CompileM Instruction
  | .when alts default => do
    let alts ← alts.mapM (λ(p, t) => do pure (p, ← splitInstruction' t))
    let code := .when alts (← splitInstruction' default)
    let index ← registerNewCode code
    return .goto index
  | .check str alt default => do
    let code := .check str (← splitInstruction' alt) (← splitInstruction' default)
    let index ← registerNewCode code
    return .goto index
  | .start prop next => do
    return .start prop (← splitInstruction' next)
  | .close prop next => do
    return .close prop (← splitInstruction'  next)
  | .store prop data next => do
    return .store prop data (← splitInstruction'  next)
  | .next num next =>  do
    return .next num (← splitInstruction' next)
  | .call func next => do
    return .call func next
  | .error nat =>
    return .error nat
  | .goto to =>
    return .goto to
  | failed =>
    return failed

def splitInstruction : Instruction → CompileM Instruction
  | .when alts default => do
    let alts ← alts.mapM (λ(p, t) => do pure (p, ← splitInstruction' t))
    return .when alts (← splitInstruction' default)
  | .check str alt default => do
    return .check str (← splitInstruction' alt) (← splitInstruction' default)
  | .start prop next => do
    return .start prop (← splitInstruction next)
  | .close prop next => do
    return .close prop (← splitInstruction next)
  | .store prop data next => do
    return .store prop data (← splitInstruction next)
  | .next num next =>  do
    return .next num (← splitInstruction next)
  | .call func next => do
    return .call func next
  | .error nat =>
    return .error nat
  | .goto to =>
    return .goto to
  | failed =>
    return failed

def splits : CompileM Unit := do
  let size ← CompileM.nodeSize
  for idx in [:size] do
    let code ← CompileM.getCode idx
    let code ← splitInstruction code
    CompileM.setMachine (Machine.setCode · idx code)

def compile (grammar: Grammar) : CompileM Unit := do
  CompileM.setMachine (λmachine => {machine with props := grammar.props.fold (λs k v => s.insert k v.value) Inhabited.default})
  specialize' grammar
  splits

def specialize (grammar: Grammar) : Except (Array (Syntax × String)) Machine :=
  let (_, machine, errs) := StateT.run (compile grammar) (Machine.new grammar.names, #[])
  if errs.isEmpty
    then .ok machine
    else .error errs
