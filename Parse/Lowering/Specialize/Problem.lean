import Parse.Lowering.Specialize.Case
import Parse.Syntax
import Lean.Data

/-!
  Definition of a [Problem] that is a matrix of problems with ASCII chars that matches some input
-/

namespace Parse.Lowering.Specialize

open Lean

abbrev Problem (α: Type) := Array (Case α)

/-- Checks if a problem will match something after specializing -/
def Problem.willMatch (problem: Problem α) (prf: Prefix) : Bool :=
  problem.any (·.subject == prf.char.toString.toSubstring)

/-- Specializes the problem with a single prefix -/
def Problem.specialize (problem: Problem α) (pref: Prefix) : Problem α :=
  problem.filterMap (Case.specialize · pref)

/-- Get the list of prefixes of the problem -/
def Problem.prefixes (problem: Problem α) : HashSet Prefix :=
  problem.filterMap Case.prefix?
  |> HashSet.insertMany Inhabited.default

/-- Gets if the problem is done (matches the input that it's specializing) -/
def Problem.getDone (problem: Problem α) : Option (Case α) := do
  let res ← problem.get? 0
  if res.subject.isEmpty then some res else none

/-- Tries to find a case that is done -/
def Problem.findDone (problem: Problem α) (otherwise: α) : Case α :=
  let res := problem.find? (·.subject.isDone)
  match res with
  | some res => res
  | none => Case.mk Subject.empty false none otherwise

/-- Gives the maximum number of steps to specialize the entire tree -/
def Problem.stepsNum (problem: Problem α) : Nat
  := problem
  |> Array.map Case.length
  |> Array.foldl Nat.max 0
  |> (· + 1)

/-- Creates a problem out of cases -/
def Problem.ofCases (case: Array Parse.Syntax.Case) : Array (Case Parse.Syntax.Action) :=
  case.concatMap (λcase => Case.ofMatcher case.action case.matcher)
