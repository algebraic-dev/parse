import Lean.Elab.Command

/-!
  High Level Syntax that is the closest to the DSL.
-/

namespace Parse.Syntax

open Lean

abbrev Tag := TSyntax `ident

/--
  A [Invoker] is a piece of syntax that represents an action that does not
  changes the string that is being matched and changes the state of the machine.
-/
inductive Invoker
  | callback (func: Syntax) (to: Tag)
  | start (prop: Tag) (to: Tag)
  | close (prop: Tag) (to: Tag)
  | store (prop: Tag) (to: Tag)
  | error (num: Syntax)
  | goto (to: Tag)
  deriving Repr, Inhabited

abbrev DupMap := HashMap Name (Array Tag)

def DupMap.add (x: Tag) (dupMap: DupMap) : DupMap :=
  let res := dupMap.findD x.getId #[]
  dupMap.insert x.getId (res.push x)

def Invoker.nodeName (map: DupMap) : Invoker → DupMap
  | .callback _ to => DupMap.add to map
  | .start _ to => DupMap.add to map
  | .close _ to => DupMap.add to map
  | .store _ to => DupMap.add to map
  | .error _ => map
  | .goto to => DupMap.add to map

/--
  A [Matcher] represents something that matches to a string, character or a change
  to another state.
-/
inductive Matcher
  | switch (syn: Lean.Syntax) (cases: Array (Syntax × String × Syntax)) (inv: Invoker)
  | is (syn: Lean.Syntax) (prop: String) (inv: Invoker)
  | select (syn: Lean.Syntax) (prop: Array (Lean.Syntax × Char)) (inv: Invoker)
  | peek (syn: Lean.Syntax) (prop: Char) (inv: Invoker)
  | otherwise (syn: Lean.Syntax) (inv: Invoker)
  | goto (syn: Lean.Syntax) (inv: Invoker)
  deriving Repr, Inhabited

def Matcher.nodeName (dupMap: DupMap) : Matcher → DupMap
  | .switch _ _ inv => inv.nodeName dupMap
  | .select _ _ inv => inv.nodeName dupMap
  | .is _ _ inv => inv.nodeName dupMap
  | .peek _ _ inv => inv.nodeName dupMap
  | .otherwise _ inv => inv.nodeName dupMap
  | .goto _ inv => inv.nodeName dupMap

/--
  A [Node] represents some state and the actions it can take to go to another state
  using matchers.
-/
structure Node where
  name  : Tag
  matchers : Array Matcher
  deriving Repr, Inhabited

def Node.nodeNames (node: Node) : DupMap :=
  node.matchers.foldl Matcher.nodeName Inhabited.default

/--
  A [Property] is some field in the data structure.
-/
structure Property where
  name  : Tag
  value : Syntax
  deriving Repr, Inhabited

/--
  Name of each one of the structures that will be generated
-/
structure Names where
  parser : Tag
  data  : Tag
  state : Tag
  callback : TSyntax `term
  errType : TSyntax `term
  deriving Repr, Inhabited

/--
  The description of a parser
-/
structure Grammar where
  names : Names
  nodes : HashMap Name Node
  props : HashMap Name Property
  deriving Inhabited

def Grammar.new (names: Names) : Grammar :=
  let default : Grammar := Inhabited.default
  { default with names }

def Grammar.addNode (grammar: Grammar) (name: Name) (to: Node) : Grammar :=
  { grammar with nodes := grammar.nodes.insert name to }

def Grammar.addProperty (grammar: Grammar) (name: Name) (to: Property) : Grammar :=
  { grammar with props := grammar.props.insert name to }

def Grammar.constainsNode (grammar: Grammar) (name: Name) : Bool :=
  grammar.nodes.contains name

def Grammar.containsProp (grammar: Grammar) (name: Name) : Bool :=
  grammar.props.contains name
