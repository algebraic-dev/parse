namespace Parse.Syntax

/-!
  High-Level Syntax Definition
-/

abbrev Goto := Nat

/-- Indicates if the capture is setting the beginning or the end of a capture -/
inductive Capture
  | begin
  | close
  | data
  deriving Inhabited, Hashable, Repr

inductive Base
  | octal
  | decimal
  | hex
  deriving Inhabited, Hashable, Repr

/-- Calls that can change the state of the parser -/
inductive Call where
  | arbitrary (name: Nat)
  | mulAdd (base: Base) (prop: Nat)
  | loadNum (prop: Nat)
  | callStore (prop: Nat) (call: Nat)
  | store (prop: Nat) (num: Nat)
  deriving Inhabited, Hashable, Repr

/-- Action that happens after something is matched with a matcher -/
inductive Action
  | store (capture: Capture) (property: Nat) (goto: Action)
  | call (callback: Call) (goto: Action)
  | goto (goto: Goto)
  | error (code: Nat)
  deriving Inhabited, Hashable, Repr

inductive MethodOrCall
  | method (name: Nat)
  | call (call: Call)
  deriving Repr, Hashable

/-- An alternative for matching strings -/
inductive Case
  | is (matchers: Array String) (action : Action)
  | peek (matchers: Array Char) (action : Action)
  | switch (matchers: Array (String × Nat)) (action : Action)
  | select (callback: MethodOrCall) (matchers: Array (Nat × Action)) (otherwise : Action)
  | goto (consume: Bool) (action : Action)
  | consume (prop: Nat) (action: Action)
  deriving Inhabited

/-- Node is some state with a bunch of matchers that can change the state and perform some actions -/
structure Node where
  name: String
  cases: Array Case
  deriving Inhabited

/-- Typ is a type representation from C -/
inductive Typ
  | u8
  | char
  | u16
  | u32
  | u64
  | span
  deriving Inhabited

/-- Storage describes each field that stores some information in -/
structure Storage where
  props: Array (String × Typ)
  callback: Array ((String × Array Nat) × Bool)
  deriving Inhabited

/-- Description of a parser -/
structure Grammar where
  storage: Storage
  nodes: Array Node
  deriving Inhabited
