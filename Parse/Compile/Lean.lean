import Lean.Elab.Command
import Lean.Parser.Term
import Lean.Parser.Do
import Lean.Parser.Extra
import Init.Meta

import Parse.Lowering
import Parse.Compile.Helpers

namespace Parse.Compile.LeanC

open Lean.Elab Command Term Lean Parser Command Std
open Parse.Syntax Parse.Lowering

/-!
  Compiles a [Parse.Syntax.Grammar] into Lean
-/

/-- State of the compilation in order to help compiling stuff. -/
structure CompileEnv where
  state : Nat
  names : Array String
  props : Array String
  calls : Array (String × Array Nat)
  maps: HashMap Interval Nat
  deriving Inhabited

abbrev Code := Array (TSyntax `Lean.Parser.Term.doSeqItem)

abbrev CompileM := StateT CompileEnv CommandElabM

def CompileM.get (f: CompileEnv -> α) : CompileM α :=
  f <$> StateT.get

def CompileM.modify (f: CompileEnv -> CompileEnv) : CompileM Unit :=
  StateT.modifyGet (((), ·) ∘ f)

def CompileM.run (c: CompileM α) : CommandElabM α :=
  Prod.fst <$> StateT.run c Inhabited.default

def CompileM.getInterval (int: Interval) : CompileM Ident := do
  let maps ← CompileM.get CompileEnv.maps
  let gen x := pure $ mkIdent $  Name.mkStr1 s!"bitmap{x}"
  if let some res := maps.find? int then
    gen res
  else do
    let size := maps.size
    CompileM.modify (λstate => { state with maps := state.maps.insert int state.maps.size })
    gen size

def internalIdent := newIdent "internalParse"

def compileTyp (_: Typ) : Ident := newIdent "Nat"

def genBitMap (name: Ident) (int: Interval) : CommandElabM (TSyntax `command) := do
  let mut alts := #[]

  for i in [0:255] do
    let int := if int.in i.toUInt8 then newIdent "true" else newIdent "false"
    alts := alts.push int

  `(def $name:ident : Array Bool := #[$(withComma alts),*])

def bitMaps (maps: HashMap Interval Nat) : CommandElabM (Array (TSyntax  `command)) := do
  let mut result := #[]

  for (int, index) in maps.toArray do
    let bitmap := s!"bitmap{index}"
    result := result.push (← genBitMap (newIdent bitmap) int)

  return result

def callbackTyp (callback: (String × Array Nat)) : CommandElabM (TSyntax `term) := do
  let ret ← `(α → IO (α × Nat))
  callback.snd.foldlM (λx _ => `(Nat → $x)) ret

def compileDataStruct (storage: Storage) : CommandElabM (TSyntax `command) := do
  let callbackFields ← storage.callback.mapM $ λ(callback, isSpan) => do
    let name := createOnIdent callback.fst
    if isSpan then
      `(structExplicitBinder| ($name:ident : Nat → Nat → ByteArray → α → IO (α × Nat)))
    else
      let typ ← callbackTyp callback
      `(structExplicitBinder| ($name:ident : $typ))

  let propFields ← storage.props.mapM $ λ(name, typ) => do
    let name := newIdent name
    let typ := compileTyp typ
    `(structExplicitBinder| ($name:ident : $typ))

  let errored ← `(structExplicitBinder| (error : Nat))
  let state ← `(structExplicitBinder| (state: $(mkIdent $ Name.mkStr1 "States")))
  let ptr ← `(structExplicitBinder| (pointer: Nat))
  let info ← `(structExplicitBinder| (info: α))

  let fields := callbackFields.append propFields
  let fields := fields.append #[errored, state, ptr, info]

  `(structure $(newIdent "Data") (α: Type) where
      $(newIdent "mk"):ident ::
      $fields*
   )

def enumStates (machine: Machine) : CommandElabM (TSyntax `command) := do
  let states ← machine.nodes.mapIdxM (λi _ => `(ctor| | $(genParseIdent "state" i):ident))
  let states := states.push (← `(ctor| | $(newIdent "failed"):ident))
  `(inductive $(newIdent "States") where
      $states*
      deriving Repr
  )

def alloyParse (name: Ident) (branches: Array (TSyntax `Lean.Parser.Term.matchAltExpr)) : CommandElabM (TSyntax `command) := do
  let alts := mkNode ``Term.matchAlts #[mkNullNode branches]
  `(partial def $name:ident
      {α: Type}
      (data: $(newIdent "Data") α)
      (input: $(newIdent "SubArray"))
      : $(newIdent "States") → IO ($(newIdent "Data") α × $(newIdent "States"))
      $alts:matchAlts)

def genCheck (code: Code) : CompileM Code := do
  let cur ← CompileM.get CompileEnv.state
  let state := genParseIdent "state" cur
  let state := mkIdent $ Name.mkStr2 "States" state.getId.toString
  return code.push (← `(Lean.Parser.Term.doSeqItem | if (input.isEmpty) then return (data, $state);))

def compileRange (name: TSyntax `term) (range: Lowering.Range) : CommandElabM (TSyntax `term) := do
  let fstChar : TSyntax `num := mkNumLit range.val.fst.toNat
  if range.val.fst != range.val.snd then
    let sndChar : TSyntax `num := mkNumLit range.val.snd.toNat
    if range.val.fst == range.val.snd - 1
      then `(($name == $fstChar || $name == $sndChar))
      else `(($name >= $fstChar && $name <= $sndChar))
  else `(($name == $fstChar))

def compileInterval (int: Interval) : CompileM (TSyntax `term) := do
  `($(← CompileM.getInterval int)[input.current.toNat]!)

def compileCheck (check: Check) : CompileM (TSyntax `term) := do
  match check with
  | .char c => `(input.current == $(mkNumLit c.toNat))
  | .range range => compileRange (← `(input.current)) range
  | .interval int => compileInterval int

mutual

partial def ifStmt (code: Code) (comparison: TSyntax `term) (ok: Instruction false) (otherwise: Instruction false) : CompileM Code := do
  let ok ← compileInstruction #[] ok
  let otherwise ← compileInstruction #[] otherwise
  let code := code.push (← `(Lean.Parser.Term.doSeqItem | if $comparison then (do $ok*) else (do $otherwise*)))
  return code

partial def compileConsumer (code: Code) : Consumer (Instruction false) → CompileM Code
  | .is str ok otherwise => do
    let cur ← CompileM.get CompileEnv.state
    let str := TSyntax.mk $ Syntax.mkStrLit str
    let state := genParseIdent "state" cur
    let state := mkIdent $ Name.mkStr2 "States" state.getId.toString
    let then_ ← compileInstruction #[] ok
    let otherwise ← compileInstruction #[] otherwise
    let stmt ← `(Lean.Parser.Term.doSeqItem |
      match $(newIdent "matchStr"):ident $str data.pointer input with
      | .paused n => do
        let data := {data with pointer := n }
        return (data, $state)
      | .failed => do
        $otherwise*
      | .succeeded => do
        $then_*
    )
    return code.push stmt
  | .char chr ok otherwise => do
    let code ← genCheck code
    let comparison ← `(input.current == $(mkNumLit chr.toNat))
    ifStmt code comparison ok otherwise
  | .range range ok otherwise => do
    let code ← genCheck code
    let comparison ← compileRange (← `(input.current)) range
    ifStmt code comparison ok otherwise
  | .map int ok otherwise => do
    let code ← genCheck code
    let comparison ← compileInterval int
    ifStmt code comparison ok otherwise
  | .chars alts otherwise => do
    let code ← genCheck code
    let otherwise ← compileInstruction #[] otherwise
    let alts ← alts.mapM $ λ(case, to) => do
      let next ← compileInstruction #[] to
      `(Lean.Parser.Term.matchAltExpr| | $(mkNumLit case.toNat) => do $next*)
    let alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | _ => do $otherwise*))
    let alts := mkNode ``Term.matchAlts #[mkNullNode alts]
    let matcher ← `(Lean.Parser.Term.«match»| match input.current with $alts)
    let matcher ← `(Lean.Parser.Term.doSeqItem| $matcher:match)
    return code.append #[matcher]
  | .mixed alts otherwise => do
    let code ← genCheck code
    let otherwise ← compileInstruction #[] otherwise
    let alts ← alts.foldlM (init := otherwise) $ λacc (check, to) => do
      let next ← compileInstruction #[] to
      let map ← compileCheck check
      return #[← `(Lean.Parser.Term.doSeqItem| if ($map) then $next* else $acc*)]
    return code.append alts

partial def compileCode (code: Code) : Call → CompileM Code
  | .arbitrary n => do
    let names ← CompileM.get CompileEnv.calls
    let propsNames ← CompileM.get CompileEnv.names
    let (name, props) := names[n]!
    let name := createOnIdent name
    let props := props.map (λprop => mkIdent $ Name.mkStr1 $ propsNames[prop]!)
    let props ← props.mapM (λprop => `(data.$prop))
    let props := Array.append props #[← `(data.info)]
    let code := code.push (← `(Lean.Parser.Term.doSeqItem| let (info, code) ← data.$name $props*))
    let code := code.push (← `(Lean.Parser.Term.doSeqItem | let data := { data with info };))
    return code
  | .mulAdd n => do
    let names ← CompileM.get CompileEnv.names
    let name := newIdent names[n]!
    return code.push (← `(Lean.Parser.Term.doSeqItem| let data := { data with $name:ident := data.$name * 10 + (input.current.toNat - 48) };))
  | .loadNum n => do
    let names ← CompileM.get CompileEnv.names
    let name := newIdent names[n]!
    return code.push (← `(Lean.Parser.Term.doSeqItem| let data := { data with $name:ident := (input.current.toNat - 48) };))
  | .callStore prop call => do
    let names ← CompileM.get CompileEnv.calls
    let propsNames ← CompileM.get CompileEnv.names
    let (name, props) := names[call]!
    let name := createOnIdent name
    let props := props.map (λprop => mkIdent $ Name.mkStr1 $ propsNames[prop]!)
    let props ← props.mapM (λprop => `(data.$prop))
    let props := Array.append props #[← `(data.info)]
    let code := code.push (← `(Lean.Parser.Term.doSeqItem| let (info, code) ← data.$name $props*))
    let names ← CompileM.get CompileEnv.names
    let name := newIdent names[prop]!
    let code := code.push (← `(Lean.Parser.Term.doSeqItem | let data := { data with $name:ident := code, info };))
    return code
  | .store method to => do
    let names ← CompileM.get CompileEnv.names
    let name := newIdent names[method]!
    return code.push (← `(Lean.Parser.Term.doSeqItem| let data := {data with $name:ident := $(mkNumLit to)};))

partial def compileInstruction (code: Code) : Instruction β → CompileM Code
  | .consumer consumer => do
    compileConsumer code consumer
  | .select call alts otherwise => do
    let code ←
      match call with
      | .call call => do
        let code ← compileCode code call
        pure (code.push (← `(Lean.Parser.Term.doSeqItem| let result := code)))
      | .method name => do
        let names ← CompileM.get CompileEnv.names
        let name := newIdent names[name]!
        pure (code.push (← `(Lean.Parser.Term.doSeqItem| let result := data.$name;)))
     let otherwise ← compileInstruction #[] otherwise
     let alts ← alts.mapM $ λ(case, to) => do
        let next ← compileInstruction #[] to
        `(Lean.Parser.Term.matchAltExpr| | $(mkNumLit case) => do $next*)
    let alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | _ => do $otherwise*))
    let alts := mkNode ``Term.matchAlts #[mkNullNode alts]
    let matcher ← `(Lean.Parser.Term.«match»| match result with $alts)
    let matcher ← `(Lean.Parser.Term.doSeqItem| $matcher:match)
    return code.push matcher
  | .store prop data next => do
    let names ← CompileM.get CompileEnv.names
    let prop := newIdent $ names.get! prop
    let data ←
      match data with
      | some data => `($(mkNumLit data))
      | none => `(input.current.toNat)
    let code := code.push (← `(Lean.Parser.Term.doSeqItem | let data := {data with $prop:ident := $data};))
    compileInstruction code next
  | .capture prop next => do
    let names ← CompileM.get CompileEnv.names
    let prop := newIdent s!"{names.get! prop}"
    let code := code.push (← `(Lean.Parser.Term.doSeqItem | let data := {data with $prop:ident := input.start};))
    compileInstruction code next
  | .consume prop next => do
    let names ← CompileM.get CompileEnv.names
    let prop := newIdent $  names.get! prop
    let code := code.push (← `(Lean.Parser.Term.doSeqItem | let input := input.consume data.$prop;))
    compileInstruction code next
  | .close prop next => do
    let names ← CompileM.get CompileEnv.names
    let name := createOnIdent names[prop]!
    let prop := newIdent names[prop]!
    let code := code.push (← `(Lean.Parser.Term.doSeqItem | let (info, code) ← data.$name data.$prop input.start input.array data.info;))
    let code := code.push (← `(Lean.Parser.Term.doSeqItem | let data := { data with info };))
    compileInstruction code next
  | .call call next => do
    let code ← compileCode code call
    compileInstruction code next
  | .next chars next => do
    let code := code.push (← `(Lean.Parser.Term.doSeqItem | let input := input.consume $(mkNumLit chars);))
    compileInstruction code next
  | .goto to => do
    let state := genParseIdent "state" to
    let state := mkIdent $ Name.mkStr2 "States" state.getId.toString
    return code.push (← `(Lean.Parser.Term.doSeqItem | $internalIdent:ident data input $state))
  | .error errCode => do
    let code := code.push (← `(Lean.Parser.Term.doSeqItem | let data := {data with error := $(mkNumLit errCode)};))
    let state := mkIdent $ Name.mkStr2 "States" "failed"
    return code.push (← `(Lean.Parser.Term.doSeqItem | return (data, $state);))

end

def compileBranch (machine: Machine) : CommandElabM (Array (TSyntax `Lean.Parser.Term.matchAltExpr) × HashMap Interval Nat) := CompileM.run do
  CompileM.modify (λstate => {state with names := machine.storage.props.map Prod.fst
                                        ,calls := machine.storage.callback.map (Prod.fst)})

  let mut branches := #[]

  for (idx, inst) in machine.nodes.mapIdx ((·, ·)) do
    CompileM.modify (λmachine => {machine with state := idx })
    let name := genParseIdent "state" idx
    let name := mkIdent $ Name.mkStr2 "States" name.getId.toString
    let alts ← compileInstruction #[] inst.instruction
    branches := branches.push (← `(Lean.Parser.Term.matchAltExpr| | $name:ident => do $alts*))

  branches := branches.push (← `(Lean.Parser.Term.matchAltExpr| | state => pure (data, state)))
  let maps ← CompileEnv.maps <$> StateT.get
  return (branches, maps)

def parser : CommandElabM (TSyntax `command) :=
  `(
    def $(newIdent "parse") {α: Type} (data: $(newIdent "Data") α) (s: ByteArray) : IO ($(newIdent "Data") α) := do
      let inp := $(mkIdent $ Name.mkStr2 "SubArray" "new") s
      let (data, res) ← $internalIdent:ident data inp data.state
      let data := {data with state := res}
      return data
  )

def create (machine: Machine) : CommandElabM (TSyntax `command) := do
  let params ← machine.storage.callback.mapM $ λ(x, isSpan) => do
    let typ ← if isSpan then `(Nat → Nat → ByteArray → α → IO (α × Nat)) else
      let ret ← `(α → IO (α × Nat))
      x.snd.foldlM (λx _ => `(Nat → $x)) ret
    `(Lean.Parser.Term.bracketedBinderF| ($(createOnIdent x.fst) : $typ))

  let binders ← machine.storage.callback.mapM $ λ(x, _) =>
    `(term| $(createOnIdent x.fst):ident )

  let props ← machine.storage.props.mapM $ λ_ => `(term| Inhabited.default)
  let name := genParseIdent "state" 0
  let name := mkIdent $ Name.mkStr2 "States" name.getId.toString

  `(
    def $(newIdent "create") {α: Type} (info: α) $params* : ($(newIdent "Data") α) :=
      $(mkIdent $ Name.mkStr2 "Data" "mk") $binders* $props* 0 $name 0 info
  )

def compile (name: Ident) (machine: Machine) : CommandElabM Unit := do
  let (branches, maps) ← compileBranch machine

  let support : Ident := mkIdent `Parse.Support

  elabCommand (← `(namespace $name))
  elabCommand (← `(open $support:ident))

  for command in (← bitMaps maps) do
    elabCommand command

  elabCommand (← enumStates machine)
  elabCommand (← compileDataStruct machine.storage)
  elabCommand (← alloyParse internalIdent branches)
  elabCommand (← parser)
  elabCommand (← create machine)
  elabCommand (← `(end $name))
