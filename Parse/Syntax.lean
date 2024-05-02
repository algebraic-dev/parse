import Lean.Data

/-!
  High level syntax that describes parsers
-/

namespace Parse.Syntax
open Lean

/-- Actions that are going to be executed after some matcher matches some input -/
inductive Action
  | store (on: Nat) (goto: Nat)
  | capture (on: Nat) (goto: Nat)
  | close (on: Nat) (goto: Nat)
  | stop (code: Nat) (goto: Nat)
  | goto (goto: Nat)
  | error (code: Nat)
  deriving Inhabited, Repr, Hashable

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
  | u16
  | u32
  | char
  | span
  deriving Inhabited

/-- Storage describes each field that stores some information in  -/
structure Storage where
  nodes: Array (String × Typ)
  deriving Inhabited

/-- Description of a parser -/
structure Grammar where
  storage: Storage
  nodes: Array Node
  deriving Inhabited
