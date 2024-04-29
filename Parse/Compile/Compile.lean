import Lean.Elab.Command
import Lean.Parser.Term
import Lean.Parser.Do
import Lean.Parser.Extra
import Parse.Compile.Tree

/-!
  Compile machines to AST
-/

open Lean.Elab Command Term Lean Parser Command Std
open Parse.Tree

abbrev Tag := TSyntax `ident

namespace Parse.Compile

-- Name functions

def stateNames (machine: Machine) : Array (String × Tag) :=
  machine.names.mapIdx $ λidx opt =>
    match opt with
    | some tag => (tag.getId.toString, tag)
    | none => (s!"state_{idx}", TSyntax.mk (mkIdent s!"state_{idx}"))

def ctorNames (names: Array (String × Tag)) : Array (TSyntax `ident) :=
  names.map (λ(name, _) => mkIdent name)

def prefixedNames (prefix_: String) (names: Array (String × Tag)) : Array (TSyntax `ident) :=
  names.map (λ(name, _) => mkIdent (Name.mkStr2 prefix_ name))

def checkStr (x: String) : Ident := mkIdent (Name.str `Parse.State.StringMatch x)

-- Compilers

partial def compileInstruction' (names: Array (TSyntax `ident)) (machine: Machine) : Instruction → CommandElabM (TSyntax `term)
  | .when alts default => do
    let mut cases := #[]

    for (p, code) in alts do
      let char := Syntax.mkLit charLitKind s!"'{p.toString}'"
      let next ← compileInstruction' names machine code
      let case ← `(Lean.Parser.Term.matchAltExpr| | $char => $next)
      cases := cases.push case

    let next ← compileInstruction' names machine default
    cases := cases.push (← `(Lean.Parser.Term.matchAltExpr| | _ => $next))
    let alts := mkNode ``Term.matchAlts #[mkNullNode cases]
    `(if s.isEmpty then (data, state, s) else match s.front with $alts)
    | .check str code default => do
      let result ← compileInstruction' names machine code
      let next ← compileInstruction' names machine default
      let term := Syntax.mkStrLit str
      `(let (result, pointer) := $(mkIdent `Parse.State.strMatch) data.pointer $term s;
        let data := {data with pointer }
        match result with
        | $(checkStr "failed") => $next
        | $(checkStr "paused") => (data, state, s.drop pointer)
        | $(checkStr "succeded") => $result)
  | .start method next => do
    let next ← compileInstruction' names machine next
    let method ← `(Lean.Parser.Term.structInstLVal | $(method):ident)
    `(let data := {data with $method := (s.startPos.byteIdx, 0)}
      $next)
  | .close method next => do
    let next ← compileInstruction' names machine next
    let ident := mkIdent (Name.mkStr2 machine.tags.data.getId.toString method.getId.toString)
    let method ← `(Lean.Parser.Term.structInstLVal | $(method):ident)
    `(let data := {data with $method := (($ident data).fst, s.startPos.byteIdx)}
      $next)
  | .store method data next => do
    let next ← compileInstruction' names machine next
    let method ← `(Lean.Parser.Term.structInstLVal | $(method):ident)
    let data := TSyntax.mk data
    `(let data := {data with $method := $data}
      $next)
  | .call data code => do
    let name := TSyntax.mk $ names.get! code
    let ident := mkIdent (Name.str machine.tags.state.getId "callback")
    let data := TSyntax.mk data
    `((data, $ident $data $name, s))
  | .error code =>
    let ident := mkIdent (Name.str machine.tags.state.getId "fail")
    let code := TSyntax.mk code
    `((data, $ident $code, s))
  | .goto code =>
    let name := TSyntax.mk $ names.get! code
    let fn := TSyntax.mk machine.tags.parser
    `($fn data $name s)
  | .next n next => do
    let next ← compileInstruction' names machine next
    let n := Syntax.mkNumLit s!"{n}"
    `(let s := s.drop $n; $next)
  | .failed =>
    let ident := mkIdent (Name.str machine.tags.state.getId "failed")
    `((data, $ident, s))

partial def compileInstruction (names: Array (TSyntax `ident)) (machine: Machine) : Instruction → CommandElabM (TSyntax `term)
  | .next n next => do `(if s.isEmpty then (data, state, s) else $(← compileInstruction' names machine (.next n next)))
  | inst => compileInstruction' names machine inst

def compileData (machine: Machine) : CommandElabM (TSyntax `command) := do
  let dataIdent := machine.tags.data
  let props := machine.props.toArray

  let props ← props.mapM (λ(name, typ) => do
    let name := mkIdent name
    let term := TSyntax.mk typ
    let exp ← `(optDeclSig| : $term)
    `(structSimpleBinder| $name:ident $exp))

  let props := props.push (← `(structSimpleBinder| pointer : Nat))
  let props ← `(structFields| $props*)

  `(structure $dataIdent where make :: $props deriving Inhabited)

def compileState (names: Array (TSyntax `ident)) (machine: Machine) : CommandElabM (TSyntax `command) := do
  let mut ctors ← names.mapM (λid => `(Lean.Parser.Command.ctor| | $id:ident))

  let errType := machine.tags.errType

  ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $(mkIdent "fail"):ident (code : $errType)))
  ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $(mkIdent "failed"):ident))

  let stateIdent := machine.tags.state
  let typ := machine.tags.callback

  ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $(mkIdent "callback"):ident (code : $typ) (next: $stateIdent)))

  let stateIdent := machine.tags.state

  `(inductive $stateIdent where $ctors* deriving Repr, Inhabited)

def compileMachine (names: Array (TSyntax `ident)) (machine: Machine) : CommandElabM (TSyntax `command) := do
  let alts ← names.mapIdxM $ λidx id => do
    let code ← compileInstruction names machine (machine.nodes.get! idx)
    `(Parser.Term.matchAltExpr | | $id => $code)

  let failIdent := mkIdent (Name.str machine.tags.state.getId "fail")
  let failedIdent := mkIdent (Name.str machine.tags.state.getId "failed")
  let callbackIdent := mkIdent (Name.str machine.tags.state.getId "callback")

  let func := machine.tags.parser

  let alts := alts.push (← `(Parser.Term.matchAltExpr | | $failIdent code => (data, $failIdent code, s)))
  let alts := alts.push (← `(Parser.Term.matchAltExpr | | $callbackIdent _ next => $func data next s))
  let alts := alts.push (← `(Parser.Term.matchAltExpr | | $failedIdent => (data, $failedIdent, s)))

  let alts := mkNode ``Term.matchAlts #[mkNullNode alts]
  let matcher ← `(match state with $alts)

  let dataIdent := machine.tags.data
  let stateIdent := machine.tags.state
  let name := machine.tags.parser

  `(partial def $name (data: $dataIdent) (state : $stateIdent) (s: Substring) : ($dataIdent × $stateIdent × Substring) := $matcher)
