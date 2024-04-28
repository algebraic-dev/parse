import Parse.Compile.Syntax
import Parse.Compile.Specialize
import Parse.Compile.Compile

import Lean.Elab.Command
import Lean.Parser.Term
import Lean.Parser.Do
import Lean.Parser.Extra

/-!
  Definition of the DSL for definining parsers for the library
-/

open Parse.Syntax
open Lean.Elab Command Term Lean Parser Command Std

-- Syntax definitions

declare_syntax_cat parsers
declare_syntax_cat clause
declare_syntax_cat invoker
declare_syntax_cat node

syntax (name := invokerCallback) "(" "callback" term "then" ident ")" : invoker
syntax (name := invokerStore) "(" "store" ident ident ")" : invoker
syntax (name := invokerStart) "(" "start" ident ident ")" : invoker
syntax (name := invokerEnd) "(" "end" ident ident ")" : invoker
syntax (name := invokerError) "(" "error" term ")" : invoker
syntax (name := invokerNode) ident : invoker

syntax (name := switchClause) "|" str "=>" term : clause

syntax (name := switchDef) "switch" invoker clause* : parsers
syntax (name := isDef) "is" str invoker : parsers
syntax (name := otherwiseDef) "otherwise" invoker : parsers
syntax (name := gotoDef) "goto" invoker : parsers
syntax (name := peekDef) "peek" char invoker : parsers

syntax (name := nodeDef) "node " ident ("where" <|> ":=") parsers* : node

syntax (name := propertyDef) "def " ident ":" term : command

-- Construction of the Syntax

def parseSwitchClause (syn: TSyntax `clause) : CommandElabM (Syntax × String × Syntax) :=
  match syn with
  | `(switchClause | | $str:str => $term) =>
    pure (syn, str.getString, term)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseInvoker : Syntax → CommandElabM Invoker
  | `(invokerCallback | (callback $id:term then $id':ident)) =>
    pure (Invoker.callback id id')
  | `(invokerStore | (store $id:ident $id':ident)) =>
    pure (Invoker.store id id')
  | `(invokerStart | (start $id:ident $id':ident)) =>
    pure (Invoker.start id id')
  | `(invokerEnd | (end $id:ident $id':ident)) =>
    pure (Invoker.close id id')
  | `(invokerError | (error $term:term)) =>
    pure (Invoker.error term)
  | `(invokerNode | $id:ident) =>
    pure (Invoker.goto id)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseMatchers (syn: TSyntax `parsers) : CommandElabM Matcher :=
  match syn with
  | `(switchDef | switch $invoker $synClauses*) => do
    let arr ← synClauses.sequenceMap parseSwitchClause
    let inv ← parseInvoker invoker
    pure (Matcher.switch syn arr inv)
  | `(isDef | is $str:str $inv) => do
    let inv ← parseInvoker inv
    pure (Matcher.is syn str.getString inv)
  | `(otherwiseDef | otherwise $inv) => do
    let inv ← parseInvoker inv
    pure (Matcher.otherwise syn inv)
  | `(gotoDef | goto $inv) => do
    let inv ← parseInvoker inv
    pure (Matcher.goto syn inv)
  | `(peekDef | peek $char:char $inv) => do
    let inv ← parseInvoker inv
    pure (Matcher.peek syn char.getChar inv)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseNode : TSyntax `nodeDef → CommandElabM Node
  | `(nodeDef| node $name where $synParsers*)
  | `(nodeDef| node $name := $synParsers*) => do
    let matchers ← synParsers.sequenceMap parseMatchers
    pure (Node.mk name matchers)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseProp : TSyntax `propertyDef → CommandElabM Property
  | `(propertyDef | def $name : $typ) =>
    pure (Property.mk name typ)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

elab "parser " name:ident " : " dataIdent:ident "," stateIdent:ident typ:term "exception" errTyp:term "where" synProps:propertyDef* synNodes:nodeDef* : command => do
  let mut grammar := Grammar.new (Names.mk name dataIdent stateIdent typ errTyp)
  let mut errored := false

  for synNode in synNodes do
    let data ← parseNode synNode
    if grammar.constainsNode data.name.getId
      then do
        Lean.logErrorAt data.name s!"duplicated node definition '{data.name.getId}'"
        errored := true
      else grammar := grammar.addNode data.name.getId data

  for synProp in synProps do
    let data ← parseProp synProp
    if grammar.containsProp data.name.getId
      then do
        Lean.logErrorAt data.name s!"duplicated property definition '{data.name.getId}'"
        errored := true
      else grammar := grammar.addProperty data.name.getId data

  match Parse.Specialize.specialize grammar with
  | .ok machine => do
    let names := Parse.Compile.stateNames machine
    let tagged := Parse.Compile.prefixedNames (machine.tags.state.getId.toString) names
    let ctors := Parse.Compile.ctorNames names

    let state ← Parse.Compile.compileState ctors machine
    let data ← Parse.Compile.compileData machine
    let definition ← Parse.Compile.compileMachine tagged machine

    elabCommand state
    elabCommand data
    elabCommand definition
  | .error res => do
    for (syn, mes) in res do
      Lean.logErrorAt syn mes

  pure ()
