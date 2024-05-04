import Lean.Elab.Command
import Lean.Parser.Term
import Lean.Parser.Do
import Lean.Parser.Extra

import Parse.Syntax
import Parse.Lowering
import Parse.Compile.C

/-!
  DSL to build a [Parse.Syntax.Grammar] and compile to a module parser inside of the module.
-/

namespace Parse.DSL

open Lean.Elab Command Term Lean Parser Command Std
open Parse.Syntax

-- Syntax definitions

declare_syntax_cat parsers
declare_syntax_cat clause
declare_syntax_cat action
declare_syntax_cat node
declare_syntax_cat typ

syntax "u8" : typ
syntax "u16" : typ
syntax "u32" : typ
syntax &"char" : typ
syntax "span" : typ

syntax (name := actionCallback) "(" "call" term "then" ident ")" : action
syntax (name := actionStore) "(" "store" ident ident ")" : action
syntax (name := actionStart) "(" "start" ident ident ")" : action
syntax (name := actionEnd) "(" "end" ident ident ")" : action
syntax (name := actionError) "(" "error" term ")" : action
syntax (name := actionNode) ident : action

syntax (name := switchClause) "|" str "=>" term : clause

syntax (name := switchDef) "switch" action clause* : parsers

syntax (name := isDef) "is" str action : parsers
syntax (name := isAllDef) "is" "[" str* "]" action : parsers

syntax (name := peekDef) "peek" char action : parsers
syntax (name := peekAllDef) "peek" "[" char* "]" action : parsers

syntax (name := otherwiseDef) "otherwise" action : parsers
syntax (name := anyDef) "any" action : parsers

syntax (name := nodeDef) "node " ident ("where" <|> ":=") parsers* : node

syntax (name := propertyDef) "def " ident ":" typ : command

syntax (name := callbackDef) &"callback " ident : command

-- Construction of the Syntax

structure Names where
  properties: HashMap String Nat
  callback: HashMap String Nat
  nodes: HashMap String Nat
  callbacks: Array String

def ensure (syn: Syntax) (name: String) (func: String → Option α) : CommandElabM α :=
  match func name with
  | some result => pure result
  | none => throwErrorAt syn s!"cannot find '{name}'"

def parseTyp : TSyntax `typ -> CommandElabM Typ
  | `(typ| u8) => pure Typ.u8
  | `(typ| u16) => pure Typ.u16
  | `(typ| u32) => pure Typ.u32
  | `(typ| span) => pure Typ.span
  | syn => do
      Lean.logInfo syn
      Lean.throwErrorAt syn "unsupported type"

def parseSwitchClause (syn: TSyntax `clause) : CommandElabM (String × Nat) :=
  match syn with
  | `(switchClause | | $str:str => $num:num) => return (str.getString, num.getNat)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseAction (names: Names) (syn: Syntax) : CommandElabM Action :=
  match syn with
  | `(actionCallback | (call $callback:ident then $to:ident)) => do
    let callback ← ensure syn callback.getId.toString names.callback.find?
    let to ← ensure syn to.getId.toString names.nodes.find?
    pure (Action.call callback to)
  | `(actionStore | (store $property:ident $to:ident)) => do
    let property ← ensure syn property.getId.toString names.properties.find?
    let to ← ensure syn to.getId.toString names.nodes.find?
    pure (Action.store Capture.data property to)
  | `(actionStart | (start $property:ident $to:ident)) => do
    let property ← ensure syn property.getId.toString names.properties.find?
    let to ← ensure syn to.getId.toString names.nodes.find?
    pure (Action.store Capture.begin property to)
  | `(actionEnd | (end $property:ident $to:ident)) => do
    let property ← ensure syn property.getId.toString names.properties.find?
    let to ← ensure syn to.getId.toString names.nodes.find?
    pure (Action.store Capture.close property to)
  | `(actionNode | $to:ident) => do
    let to ← ensure syn to.getId.toString names.nodes.find?
    pure (Action.goto to)
  | `(actionError | (error $num:num)) =>
    pure (Action.error num.getNat)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseMatchers (names: Names) (syn: TSyntax `parsers) : CommandElabM Case :=
  match syn with
  | `(switchDef | switch $action $synClauses*) => do
    let arr ← synClauses.sequenceMap parseSwitchClause
    let inv ← parseAction names action
    pure (Case.mk (Matcher.select arr) inv)
  | `(isDef | is $str:str $inv) => do
    let inv ← parseAction names inv
    pure (Case.mk (Matcher.is #[str.getString]) inv)
  | `(isAllDef | is [ $str:str* ] $inv) => do
    let inv ← parseAction names inv
    pure (Case.mk (Matcher.is (str.map (·.getString))) inv)
  | `(peekDef | peek $chr:char $inv) => do
    let inv ← parseAction names inv
    pure (Case.mk (Matcher.peek #[chr.getChar]) inv)
  | `(peekAllDef | peek [ $chr:char* ] $inv) => do
    let inv ← parseAction names inv
    pure (Case.mk (Matcher.peek (chr.map (·.getChar))) inv)
  | `(anyDef | any $inv) => do
    let inv ← parseAction names inv
    pure (Case.mk (Matcher.goto true) inv)
  | `(otherwiseDef | otherwise $inv) => do
    let inv ← parseAction names inv
    pure (Case.mk (Matcher.goto false) inv)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseNode (names: Names) : TSyntax `Parse.DSL.nodeDef → CommandElabM Node
  | `(nodeDef| node $name where $synParsers*)
  | `(nodeDef| node $name := $synParsers*) => do
    let matchers ← synParsers.sequenceMap (parseMatchers names)
    pure (Node.mk name.getId.toString matchers)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseProp : TSyntax `Parse.DSL.propertyDef → CommandElabM (String × Typ)
  | `(propertyDef | def $name : $typ) => do
    let typ ← parseTyp typ
    pure (name.getId.toString, typ)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseCall : TSyntax `Parse.DSL.callbackDef → CommandElabM String
  | `(callbackDef | callback $name) => pure name.getId.toString
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def getNodeName : TSyntax `Parse.DSL.nodeDef → CommandElabM String
  | `(nodeDef| node $name where $_*)
  | `(nodeDef| node $name := $_*) => pure name.getId.toString
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def arrToMap [BEq α] [Hashable α] (arr: Array α) : HashMap α Nat :=
  arr.mapIdx ((·, ·))
  |> Array.foldl (λmap (idx, value) => map.insert value idx) HashMap.empty

elab "parser " name:ident "where" synProps:propertyDef* synCalls:callbackDef* synNodes:nodeDef* : command => do
  let props ← synProps.mapM parseProp

  let nodeNames ← synNodes.mapM getNodeName
  let propNames := props.map Prod.fst

  let callNames ← synCalls.mapM (λx => (·, false) <$> parseCall x)

  -- Add callback for spans
  let callNames := callNames.append (props.filterMap $ λx => match x.snd with |.span => (x.fst, true) | _ => none)

  let callStrs := callNames.map Prod.fst
  let names := Names.mk (arrToMap propNames) (arrToMap callStrs) (arrToMap nodeNames) callStrs

  let nodes ← synNodes.mapM (parseNode names)
  let storage := Storage.mk props callNames

  let grammar := Grammar.mk storage nodes
  let machine := Parse.Lowering.translate grammar

  let res ← Parse.Compile.C.compile name machine

  elabCommand res
