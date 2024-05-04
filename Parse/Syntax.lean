/-!
  High-Level Syntax Definition
-/

namespace Parse.Syntax

abbrev Goto := Nat

/-- Indicates if the capture is setting the beginning or the end of a capture -/
inductive Capture
  | begin
  | close
  | data
  deriving Inhabited, Hashable, Repr

/-- Action that happens after something is matched with a matcher -/
inductive Action
  | store (capture: Capture) (property: Nat) (goto: Goto)
  | call (callback: Nat) (goto: Goto)
  | goto (goto: Goto)
  | error (code: Nat)
  deriving Inhabited, Hashable, Repr

/-- An alternative for matching strings -/
inductive Matcher
  | is (matchers: Array String)
  | peek (matchers: Array Char)
  | select (matchers: Array (String × Nat))
  | goto (consume: Bool)
  deriving Inhabited

/-- A matcher for a string and the consequence of matching it -/
structure Case where
  matcher : Matcher
  action : Action
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
  | span
  deriving Inhabited

/-- Storage describes each field that stores some information in  -/
structure Storage where
  nodes: Array (String × Typ)
  callback: Array String
  deriving Inhabited

/-- Description of a parser -/
structure Grammar where
  storage: Storage
  nodes: Array Node
  deriving Inhabited
