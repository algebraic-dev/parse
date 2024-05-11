import Parse.Syntax

namespace Parse.Lowering.Specialize

/-!
  Definition of a [Case] that is something that is in the middle of a match problem
-/

-- Just to be able to hash prefixes
scoped instance : Hashable Char where
  hash x := x.val.toUInt64

/-- The prefix is something that can be used inside a match to go another state -/
structure Prefix where
  char : Char
  capture : Bool
  deriving Repr, Hashable, BEq, Inhabited

inductive Action where
  | single (act: Syntax.Action)
  | select (call: Syntax.MethodOrCall) (acts: Array (Nat × Syntax.Action)) (otherwise: Syntax.Action)

/-- Subject is the string to test -/
def Subject := Substring
  deriving BEq, Repr

def Subject.empty : Subject := "".toSubstring

/-- Check if the subject is done matching -/
def Subject.isDone (sub: Subject) : Bool := sub.isEmpty

/-- Removes one prefix from the Subject -/
def Subject.next (sub: Subject) : Subject := sub.drop 1

/-- Some case to match inside the match array -/
structure Case (α: Type) where
  subject : Subject
  capture : Bool
  store : Option Nat
  action : α
  deriving Repr

/-- Gets the prefix of a subject -/
def Case.prefix? (sub: Case α) : Option Prefix :=
  if sub.subject.isDone
    then none
    else some { char := sub.subject.front, capture := sub.capture }

/-- Specializes the case to a certain prefix if the prefix matches -/
def Case.specialize (case: Case α) (pref: Prefix) : Option (Case α) :=
  if case.prefix? == some pref
    then some { case with subject := case.subject.next }
    else if case.subject.isEmpty then some case else none

/-- Size of a case -/
def Case.length (case: Case α) := case.subject.bsize

/-- Creates a case from a matcher and action -/
def Case.ofMatcher : Parse.Syntax.Case → Array (Case Action)
  | .is strs action =>
      strs.map ({subject := ·.toSubstring, capture := true, store := none, action := Action.single action })
  | .peek chars action =>
      chars.map ({subject := ·.toString.toSubstring, capture := false, store := none, action := Action.single action })
  | .switch cases action=>
      cases.map (λ(str, data) => {subject := str.toSubstring, capture := true, store := some data, action := Action.single action })
  | .goto capture action =>
      #[{subject := "".toSubstring, capture, store := none, action := Action.single action }]
  | .select inv actions otherwise =>
      #[{subject := "".toSubstring, capture := false, store := none, action := Action.select inv actions otherwise }]
