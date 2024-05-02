import Parse.Syntax
import Lean.Data

/-!
  Specialization of matchers to case trees
-/

namespace Parse.Specialize

open Parse.Syntax Lean

scoped instance : Hashable Char where
  hash c := c.val.toUInt64

/-- The prefix is something that can be used inside a match to go another state -/
structure Prefix where
  char : Char
  capture : Bool
  deriving Repr, Hashable, BEq, Inhabited

/-- Subject is the string to test -/
def Subject := Substring
  deriving BEq, Repr

/-- Check if the subject is done matching -/
def Subject.isDone (sub: Subject) : Bool :=
  sub.isEmpty

/-- Removes one prefix from the Subject -/
def Subject.next (sub: Subject) : Subject :=
  sub.drop 1

/-- Some case to match inside the match array -/
structure Case where
  subject : Subject
  capture : Bool
  store : Option Nat
  action : Action
  deriving Repr

/-- Gets the prefix of a subject -/
def Case.prefix? (sub: Case) : Option Prefix :=
  if sub.subject.isDone
    then none
    else some { char := sub.subject.front, capture := sub.capture }

def Case.specialize (case: Case) (pref: Prefix) : Option Case :=
  if case.prefix? == some pref
    then some { case with subject := case.subject.next }
    else if case.subject.isEmpty then some case else none

abbrev Problem := Array Case

def Matcher.fromMatcher (action: Action) : Matcher → Array Case
  | .is strs =>
      strs.map ({subject := ·.toSubstring, capture := true, store := none, action })
  | .peek chars =>
      chars.map ({subject := ·.toString.toSubstring, capture := false, store := none, action })
  | .select cases =>
      cases.map (λ(str, data) => {subject := str.toSubstring, capture := true, store := some data, action })
  | .goto capture =>
      #[{subject := "".toSubstring, capture, store := none, action }]

def Problem.willMatch (problem: Problem) (prf: Prefix) : Bool :=
  problem.any (·.subject == prf.char.toString.toSubstring)

def Problem.fromCases (case: Array Parse.Syntax.Case) : Array Case :=
  case.concatMap (λcase => Matcher.fromMatcher case.action case.matcher)

def Problem.filterByPrefix (problem: Problem) (pref: Prefix) : Problem :=
  problem.filterMap (Case.specialize · pref)

def Problem.prefixes (problem: Problem) : Array Prefix :=
  let hashSet : HashSet Prefix := Inhabited.default
  problem.filterMap Case.prefix?
  |> HashSet.insertMany hashSet
  |> HashSet.toArray

def Problem.getDone (problem: Problem) : Option Case := do
  let res ← problem.get? 0
  if res.subject.isEmpty then some res else none

def Problem.findDone (problem: Problem) : (Option Nat × Bool × Action) :=
  let res := (λc => (c.store, c.capture, c.action)) <$> problem.find? (·.subject.isDone)
  match res with
  | some res => res
  | none => (none, false, Action.error 0)

structure Branch (k: Type) (v: Type) where
  subject: k
  capture: Bool
  next: v
  deriving Hashable, Repr

inductive Branches (α: Type)
  | str (next: Branch String α)
  | chars (chars: Array (Branch Char α))
  deriving Hashable, Repr

inductive Tree where
  | done (data: Option Nat) (capture: Bool) (action: Action)
  | fail
  | branch (cases: Branches Tree) (default: Option Nat × Bool × Action)
  deriving Hashable, Repr, Inhabited

partial def Problem.accumulate (problem: Problem) (acc: String) : (Problem × String) :=
  let prefixes := problem.prefixes
  if prefixes.size == 1
    then let char := prefixes.get! 0
         if problem.willMatch char
            then (problem.filterByPrefix char, acc.push char.char)
            else Problem.accumulate (problem.filterByPrefix char) (acc.push char.char)
    else (problem, acc)

partial def Problem.specialize (problem: Problem) : Tree :=
  if problem.isEmpty then Tree.fail else
  if let some res := problem.getDone
    then Tree.done res.store res.capture res.action
    else let otherwise := problem.findDone
         let (problem₂, acc) := Problem.accumulate problem ""
         match acc.length with
         | 0 => let prefixes := problem₂.prefixes
                let chars := prefixes.map (λp => Branch.mk p.char p.capture (problem₂.filterByPrefix p).specialize)
                Tree.branch (Branches.chars chars) otherwise
         | 1 => let p := problem.prefixes.get! 0
                Tree.branch (Branches.chars #[Branch.mk p.char p.capture problem₂.specialize]) otherwise
         | _ => Tree.branch (Branches.str (Branch.mk acc true (problem₂.specialize))) otherwise
