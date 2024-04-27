import Lean.Elab.Command
import Lean.Parser.Term
import Lean.Parser.Do
import Lean.Parser.Extra

import Parse.Data

/-!
  Module describing the DSL for building a grammar into lean4 code into the project
-/

namespace Parse.DSL

open Lean.Elab Command Term Lean Parser Command Std
open Parse.HS

-- Syntax definition

declare_syntax_cat parsers
declare_syntax_cat clause
declare_syntax_cat invoker

syntax (name := invokerCallback) "(" "callback" ident ident ")" : invoker
syntax (name := invokerStore) "(" "store" ident ident ")" : invoker
syntax (name := invokerStart) "(" "start" ident ident ")" : invoker
syntax (name := invokerEnd) "(" "end" ident ident ")" : invoker
syntax (name := invokerError) "(" "error" num ")" : invoker
syntax (name := invokerNode) ident : invoker

syntax (name := switchClause) "|" str "=>" term : clause

syntax (name := switchDef) "switch" invoker clause* : parsers
syntax (name := isDef) "is" str invoker : parsers
syntax (name := otherwiseDef) "otherwise" invoker : parsers
syntax (name := gotoDef) "goto" invoker : parsers
syntax (name := peekDef) "peek" char invoker : parsers

syntax (name := nodeDef)
  "node " ident "where" parsers* : command

syntax (name := propertyDef)
  "def " ident ":" term : command

-- Definition

def parseSwitchClause : TSyntax `clause → CommandElabM (String × Syntax)
  | `(switchClause | | $str:str => $term) =>
    pure (str.getString, term)
  | _ => throwUnsupportedSyntax

def parseInvoker : Syntax → CommandElabM Invoker
  | `(invokerCallback | (callback $id:ident $id':ident)) =>
    pure (Invoker.callback id.getId id'.getId)
  | `(invokerStore | (store $id:ident $id':ident)) =>
    pure (Invoker.store id.getId id'.getId)
  | `(invokerStart | (start $id:ident $id':ident)) =>
    pure (Invoker.store id.getId id'.getId)
  | `(invokerEnd | (end $id:ident $id':ident)) =>
    pure (Invoker.close id.getId id'.getId)
  | `(invokerError | (error $num:num)) =>
    pure (Invoker.error num.getNat)
  | `(invokerNode | $id:ident) =>
    pure (Invoker.goto id.getId)
  | f => throwUnsupportedSyntax

def parseMatchers : TSyntax `parsers → CommandElabM Matcher
  | `(switchDef | switch $invoker $synClauses*) => do
    let arr ← synClauses.sequenceMap parseSwitchClause
    let inv ← parseInvoker invoker
    pure (Matcher.switch arr inv)
  | `(isDef | is $str:str $inv) => do
    let inv ← parseInvoker inv
    pure (Matcher.is str.getString inv)
  | `(otherwiseDef | otherwise $inv) => do
    let inv ← parseInvoker inv
    pure (Matcher.otherwise inv)
  | `(gotoDef | goto $inv) => do
    let inv ← parseInvoker inv
    pure (Matcher.goto inv)
  | `(peekDef | peek $char:char $inv) => do
    let inv ← parseInvoker inv
    pure (Matcher.peek char.getChar inv)
  | f => throwUnsupportedSyntax

def parseProp : TSyntax `Parse.DSL.propertyDef → CommandElabM Property
  | `(propertyDef | def $name : $typ) =>
    pure (Property.mk name.getId typ)
  | _ => throwUnsupportedSyntax

def parseNode : TSyntax `Parse.DSL.nodeDef → CommandElabM Node
  | `(nodeDef| node $name where $synParsers*) => do
    let matchers ← synParsers.sequenceMap parseMatchers
    pure (Node.mk name.getId matchers)
  | _ => throwUnsupportedSyntax

def identMk (num: Nat) : TSyntax `ident :=
  mkIdent s!"state_{num}"

def mkRange (to: Nat) (f: Nat → α) : Array α := Id.run do
  let mut arr := #[]
  for i in [0:to] do arr := arr.push (f i)
  return arr


partial def compileInstructions' (fn: Syntax) (names: Array Syntax) : List LS.Instruction → CommandElabM (TSyntax `term)
  | [] => `((data, GState.fail 0, s))
  | x :: xs =>
    match x with
    | .when alts => do
      let mut cases := #[]

      for (p, code) in alts do
        let char := Syntax.mkLit charLitKind s!"'{p.toString}'"
        let next ← compileInstructions' fn names code.toList
        let case ← `(Lean.Parser.Term.matchAltExpr| | $char => $next)
        cases := cases.push case

      let next ← compileInstructions' fn names xs
      cases := cases.push (← `(Lean.Parser.Term.matchAltExpr| | _ => $next))

      let alts := mkNode ``Term.matchAlts #[mkNullNode cases]

      `(match s.front with $alts)
    | .check str code => do
      let result ← compileInstructions' fn names code.toList
      let next ← compileInstructions' fn names xs
      let term := Syntax.mkStrLit str
      let checkStr x := mkIdent (Name.str `Parse.DSL.CheckStr x)
      `(let (data, result, s) := checkStr data $term s;
        match result with
        | $(checkStr "failed") => $next
        | $(checkStr "paused") => (data, state, s)
        | $(checkStr "finished") => $result)
    | .callback _ => `((data, state, s))
    | .start method => do
      let next ← compileInstructions' fn names xs
      let method ← `(Lean.Parser.Term.structInstLVal | $(mkIdent method):ident)
      `(let data := {data with $method := (s.startPos.byteIdx, 0)}
        $next)
    | .close method => do
      let next ← compileInstructions' fn names xs
      let ident := mkIdent (Name.mkStr2 "GData" method.toString)
      let method ← `(Lean.Parser.Term.structInstLVal | $(mkIdent method):ident)
      `(let data := {data with $method := (($ident data).fst, s.startPos.byteIdx)}
        $next)
    | .store method data => do
      let next ← compileInstructions' fn names xs
      let method ← `(Lean.Parser.Term.structInstLVal | $(mkIdent method):ident)
      let data := TSyntax.mk data
      `(let data := {data with $method := $data}
        $next)
    | .error code =>
      let name := Syntax.mkNumLit (reprStr code)
      `((data, GState.fail $name, s))
    | .goto code =>
      let name := TSyntax.mk $ names.get! code
      let fn := TSyntax.mk fn
      `($fn data $name s)
    | .next n => do
      let next ← compileInstructions' fn names xs
      let n := Syntax.mkNumLit s!"{n}"
      `(let s := s.drop $n
       $next
       )

def isWhen : LS.Instruction → Bool
  | .when _ => true
  | _     => false

def compileInstructions (fn: Syntax) (names: Array Syntax) (code: Array LS.Instruction) : CommandElabM (TSyntax `term) :=
  if let some fst := code.find? isWhen
    then do
      let res ← compileInstructions' fn names code.toList
      match fst with
      | .when _ => `(if s.isEmpty then (data, state, s) else $res)
      | _       => pure res
    else compileInstructions' fn names code.toList

inductive CheckStr where
  | failed
  | finished
  | paused

elab "parser " name:ident "where" synProps:propertyDef* synNodes:nodeDef* : command => do
  let nodes ← synNodes.sequenceMap parseNode
  let props ← synProps.sequenceMap parseProp

  let grammar := Grammar.mk name.getId nodes props

  match Parse.LS.Grammar.compile grammar with
  | Except.error err => Lean.logError ("err: " ++ (reprStr err))
  | Except.ok grammar => do

    Lean.logInfo (Parse.LS.Grammar.toStr grammar)

    let grammar := Parse.LS.Grammar.split grammar
    let mut rawName := mkRange grammar.nodes.size (s!"state_{·}")
    let mut ctorsName : Array (TSyntax `ident) := rawName.map (mkIdent ∘ Name.mkStr1)
    let fullNames := rawName.map (λx => Lean.mkIdent (Name.mkStr2 "GState" x))
    let stateIdent := mkIdent `GState

    let mut ctors ← ctorsName.mapM (λid => `(Lean.Parser.Command.ctor| | $id:ident))
    ctors := ctors.push (← `(Lean.Parser.Command.ctor| | fail (code : Nat)))

    let inductiv ← `(inductive $stateIdent where $ctors* deriving Repr, Inhabited)
    elabCommand inductiv

    let props ← grammar.props.mapM (λ(name, typ) => do
      let name := mkIdent name
      let term := TSyntax.mk typ
      let exp ← `(optDeclSig| : $term)
      `(structSimpleBinder| $name:ident $exp))

    let dataIdent := mkIdent `GData

    let props := props.push (← `(structSimpleBinder| pointer : Nat))

    let ata ← `(structFields| $props*)
    let struc ← `(structure $dataIdent where make :: $ata deriving Inhabited)
    elabCommand struc

    let alts ← (fullNames.zip (mkRange (grammar.nodes.size + 1) (·))).mapM $ λ(id, idx) => do
      let code ← compileInstructions name fullNames (grammar.nodes.get! idx)
      `(Parser.Term.matchAltExpr | | $id => $code)

    let alts := alts.push (← `(Parser.Term.matchAltExpr | | GState.fail code => (data, GState.fail code, s)))

    let alts := mkNode ``Term.matchAlts #[mkNullNode alts]
    let matcher ← `(match state with $alts)
    let definition ← `(partial def $name (data: $dataIdent) (state : $stateIdent) (s: Substring) : ($dataIdent × $stateIdent × Substring) := $matcher)
    elabCommand (← `(def checkStr (g: $dataIdent) (s: String) (su: Substring) : ($dataIdent × $(mkIdent `Parse.DSL.CheckStr) × Substring) := Id.run do
                      let mut checkAgainst := s.toSubstring.drop g.pointer
                      let mut current := su

                      let minSize := Nat.min checkAgainst.bsize current.bsize
                      dbg_trace s!"comparing {checkAgainst} : {current} // {minSize}"

                      for _ in [:minSize] do
                        let (l, r) := (checkAgainst.front, current.front)
                        checkAgainst := checkAgainst.drop 1
                        current := current.drop 1

                        dbg_trace (l, r)

                        if l != r then
                          return (g, $(mkIdent `Parse.DSL.CheckStr.failed) ,su)

                      if checkAgainst.bsize != 0
                        then ({g with pointer := s.length - checkAgainst.bsize}, $(mkIdent `Parse.DSL.CheckStr.paused),su)
                        else (g, $(mkIdent `Parse.DSL.CheckStr.finished), su)
                      ))
    elabCommand definition

parser parseHttp where
    def method : Nat
    def url    : Nat × Nat

    node method where
        switch (store method beforeUrl)
            | "HEAD" => 0
        goto (error 1)

    node beforeUrl where
        is " " beforeUrl
        otherwise (start url url)

    node url where
        peek ' ' (end url http)
        otherwise url

    node http where
        is " HTTP/1.1\r\n\r\n" complete
        goto (error 6)
