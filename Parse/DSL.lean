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
declare_syntax_cat selectClause
declare_syntax_cat action
declare_syntax_cat action_enclose
declare_syntax_cat node
declare_syntax_cat code
declare_syntax_cat typ

syntax ":" &"u8" : typ
syntax ":" &"u16" : typ
syntax ":" &"u32" : typ
syntax ":" &"u64" : typ
syntax ":" &"char" : typ
syntax ":" &"span" : typ

syntax (name := callCode) "(" &"mulAdd" ident ")" : code
syntax (name := callLoad) "(" &"loadNum" ident ")" : code
syntax (name := callStore) "(" &"callStore" ident ident ")" : code
syntax (name := callIdent) ident : code

syntax (name := actionCallback) "call" code ident : action
syntax (name := actionStore) "store" ident ident : action
syntax (name := actionStart) "start" ident ident : action
syntax (name := actionEnd) "end" ident ident : action
syntax (name := actionConsume) "consume" ident ident : action
syntax (name := actionError) "error" term : action
syntax (name := actionNode) ident : action

syntax (name := actionEnclosePar) "(" action ")" : action_enclose
syntax (name := actionEnclose) action : action_enclose

syntax (name := switchClause) "|" str "=>" term : clause
syntax (name := selectClause) "|" num "=>" action : selectClause

syntax (name := switchDef) "switch" action_enclose clause* : parsers
syntax (name := selectIdentDef) "select" "(" &"read" ident ")" selectClause* : parsers
syntax (name := selectDef) "select" code selectClause* : parsers

syntax (name := isDef) "is" str action_enclose : parsers
syntax (name := isIdentDef) "is" ident action_enclose : parsers
syntax (name := isAllDef) "is" "[" str* "]" action_enclose : parsers

syntax (name := peekDef) "peek" char action_enclose : parsers
syntax (name := peekAllDef) "peek" "[" char* "]" action_enclose : parsers

syntax (name := otherwiseDef) "otherwise" action_enclose : parsers
syntax (name := anyDef) "any" action_enclose : parsers

syntax (name := nodeDef) "node " ident ("where" <|> ":=") parsers* : node

syntax (name := propertyDef) "def " ident typ : command
syntax (name := setDef) "set " ident ":=" "[" str* "]" : command

syntax (name := callbackDef) &"callback " ident : command

-- Construction of the Syntax

structure Names where
  definitions: HashMap String (Array String)
  properties: HashMap String Nat
  callback: HashMap String Nat
  nodes: HashMap String Nat
  callbacks: Array String

def ensure (syn: Syntax) (name: String) (func: String → Option α) : CommandElabM α :=
  match func name with
  | some result => pure result
  | none => throwErrorAt syn s!"cannot find '{name}'"

def parseTyp : TSyntax `typ -> CommandElabM Typ
  | `(typ| : u8) => pure Typ.u8
  | `(typ| : u16) => pure Typ.u16
  | `(typ| : u32) => pure Typ.u32
  | `(typ| : u64) => pure Typ.u64
  | `(typ| : span) => pure Typ.span
  | syn => do
      Lean.logInfo syn
      Lean.throwErrorAt syn "unsupported type"

def parseSwitchClause (syn: TSyntax `clause) : CommandElabM (String × Nat) :=
  match syn with
  | `(switchClause | | $str:str => $num:num) => return (str.getString, num.getNat)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseCode (names: Names) (syn: Syntax) : CommandElabM Call :=
  match syn with
  | `(callCode| (mulAdd $callback:ident)) => do
    let property ← ensure syn callback.getId.toString names.properties.find?
    return (Call.mulAdd property)
  | `(callLoad| (loadNum $callback:ident)) => do
    let property ← ensure syn callback.getId.toString names.properties.find?
    return (Call.loadNum property)
  | `(callStore| (callStore $callback:ident $prop:ident)) => do
    let callback ← ensure syn callback.getId.toString names.callback.find?
    let property ← ensure syn prop.getId.toString names.properties.find?
    return (Call.callStore property callback)
  | `(callIdent| $callback:ident) => do
    let callback ← ensure syn callback.getId.toString names.callback.find?
    return (Call.arbitrary callback)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseAction (names: Names) (syn: TSyntax `action) : CommandElabM Action :=
  match syn with
  | `(actionCallback | call $code:code $to:ident) => do
    let code ← parseCode names code
    let to ← ensure syn to.getId.toString names.nodes.find?
    pure (Action.call code to)
  | `(actionStore | store $property:ident $to:ident) => do
    let property ← ensure syn property.getId.toString names.properties.find?
    let to ← ensure syn to.getId.toString names.nodes.find?
    pure (Action.store Capture.data property to)
  | `(actionStart | start $property:ident $to:ident) => do
    let property ← ensure syn property.getId.toString names.properties.find?
    let to ← ensure syn to.getId.toString names.nodes.find?
    pure (Action.store Capture.begin property to)
  | `(actionEnd | end $property:ident $to:ident) => do
    let property ← ensure syn property.getId.toString names.properties.find?
    let to ← ensure syn to.getId.toString names.nodes.find?
    pure (Action.store Capture.close property to)
  | `(actionNode | $to:ident) => do
    let to ← ensure syn to.getId.toString names.nodes.find?
    pure (Action.goto to)
  | `(actionConsume | consume $prop:ident $to:ident) => do
    let property ← ensure syn prop.getId.toString names.properties.find?
    let to ← ensure syn to.getId.toString names.nodes.find?
    pure (Action.consume property to)
  | `(actionError | error $num:num) =>
    pure (Action.error num.getNat)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseSelectClause (names: Names) (syn: TSyntax `selectClause) : CommandElabM (Nat × Action) :=
  match syn with
  | `(selectClause | | $num:num => $action:action) => return (num.getNat, ← parseAction names action)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseEnclose (names: Names) (syn: TSyntax `action_enclose) : CommandElabM Action :=
  match syn with
  | `(actionEnclosePar| ( $action ))
  | `(actionEnclose| $action) => parseAction names action
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseMatchers (names: Names) (syn: TSyntax `parsers) : CommandElabM Case :=
  match syn with
  | `(switchDef | switch $action $synClauses*) => do
    let arr ← synClauses.sequenceMap parseSwitchClause
    let inv ← parseEnclose names action
    pure (Case.switch arr inv)
  | `(selectIdentDef | select (read $property:ident) $synClauses*) => do
    let property ← ensure syn property.getId.toString names.properties.find?
    let arr ← synClauses.sequenceMap (parseSelectClause names)
    pure (Case.select (MethodOrCall.method property) arr)
  | `(selectDef | select $caller:code $synClauses*) => do
    let inv ← parseCode names caller
    let arr ← synClauses.sequenceMap (parseSelectClause names)
    pure (Case.select (MethodOrCall.call inv) arr)
  | `(isDef | is $str:str $inv) => do
    let inv ← parseEnclose names inv
    pure (Case.is #[str.getString] inv)
  | `(isIdentDef | is $ident $inv) => do
    let sets := names.definitions.find? ident.getId.toString
    match sets with
    | some sets =>
      let inv ← parseEnclose names inv
      pure (Case.is sets inv)
    | none =>
      throwErrorAt ident s!"cannot string set '{ident.getId.toString}'"
  | `(isAllDef | is [ $str:str* ] $inv) => do
    let inv ← parseEnclose names inv
    pure (Case.is (str.map (·.getString)) inv)
  | `(peekDef | peek $chr:char $inv) => do
    let inv ← parseEnclose names inv
    pure (Case.peek #[chr.getChar] inv)
  | `(peekAllDef | peek [ $chr:char* ] $inv) => do
    let inv ← parseEnclose names inv
    pure (Case.peek (chr.map (·.getChar)) inv)
  | `(anyDef | any $inv) => do
    let inv ← parseEnclose names inv
    pure (Case.goto true inv)
  | `(otherwiseDef | otherwise $inv) => do
    let inv ← parseEnclose names inv
    pure (Case.goto false inv)
  | syn => Lean.throwErrorAt syn "unsupported matcher"

def parseNode (names: Names) : TSyntax `Parse.DSL.nodeDef → CommandElabM Node
  | `(nodeDef| node $name where $synParsers*)
  | `(nodeDef| node $name := $synParsers*) => do
    let matchers ← synParsers.sequenceMap (parseMatchers names)
    pure (Node.mk name.getId.toString matchers)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def parseProp : TSyntax `Parse.DSL.propertyDef → CommandElabM (String × Typ)
  | `(propertyDef | def $name $typ) => do
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

def parseSet : TSyntax `Parse.DSL.setDef → CommandElabM (String × Array String)
  | `(setDef | set $name := [ $str:str* ]) => pure (name.getId.toString, str.map TSyntax.getString)
  | syn => Lean.throwErrorAt syn "unsupported syntax"

def arrToMap [BEq α] [Hashable α] (arr: Array α) : HashMap α Nat :=
  arr.mapIdx ((·, ·))
  |> Array.foldl (λmap (idx, value) => map.insert value idx) HashMap.empty

elab "parser " name:ident "where" synProps:propertyDef* synSet:setDef* synCalls:callbackDef* synNodes:nodeDef* : command => do
  let props ← synProps.mapM parseProp

  let nodeNames ← synNodes.mapM getNodeName
  let propNames := props.map Prod.fst

  let setNames ← synSet.mapM parseSet

  let callNames ← synCalls.mapM (λx => (·, false) <$> parseCall x)

  -- Add callback for spans
  let callNames := callNames.append (props.filterMap $ λx => match x.snd with |.span => (x.fst, true) | _ => none)

  let callStrs := callNames.map Prod.fst
  let names := Names.mk (HashMap.ofList setNames.toList) (arrToMap propNames) (arrToMap callStrs) (arrToMap nodeNames) callStrs

  let nodes ← synNodes.mapM (parseNode names)
  let storage := Storage.mk props callNames

  let grammar := Grammar.mk storage nodes
  let machine := Parse.Lowering.translate grammar

  Parse.Compile.C.compile name machine
