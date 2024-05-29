import Parse.Lowering.Specialize.Problem
import Parse.Lowering.Specialize.Case
import Parse.Lowering.Interval
import Parse.Syntax

namespace Parse.Lowering.Specialize

open Parse.Lowering.Interval
open Parse.Syntax

/-!
  This module specializes a bunch of parsers that looks like pattern match to a tree that matches
  one thing at a time.
-/

abbrev Fuel := Nat

/-- Match is what checks a subject and what says what`s next after matching -/
structure Match (k: Type) (v: Type) where
  subject: k
  capture: Bool
  next: v
  deriving Hashable, Repr

/-- The action and some info to execute after matching something -/
structure Step (α: Type) where
  data: Option Nat
  capture: Bool
  next: α
  deriving Hashable, Repr

def Step.ofCase (case: Case α) : Step α :=
  Step.mk case.store case.capture case.action

/-- Branches of different types -/
inductive Branch (α: Type)
  | string (next: Match String α)
  | chars (chars: Array (Match Char α))
  deriving Hashable, Repr

/-- Matching tree -/
inductive Tree (α: Type) where
  | branch (cases: Branch (Tree α)) (default: Tree α)
  | consume (method: Nat) (step: Step α)
  | done (step: Step α)
  | fail
  deriving Hashable, Repr, Inhabited

def Problem.accumulate (problem: Problem α) (acc: String) : Fuel → (Problem α × String)
  | 0 => (problem, acc)
  | n + 1 =>
    let prefixes := problem.prefixes
    if prefixes.size == 1 then
      let char := prefixes.toArray.get! 0
      if problem.willMatch char
        then (problem.specialize char, acc.push char.char)
        else Problem.accumulate (problem.specialize char) (acc.push char.char) n
    else (problem, acc)

def Problem.solve' (problem: Problem Action) : Nat → Tree Action
  | 0 => Tree.fail
  | n + 1 =>
    if problem.isEmpty then Tree.fail else
    if let some res := problem.getDone then
      match res.read with
      | some method => Tree.consume method (Step.mk res.store res.capture res.action)
      | none => Tree.done (Step.mk res.store res.capture res.action)
    else
      let otherwise := problem.findDone (.single (Action.error 1))
      let (problem₂, acc) := Problem.accumulate problem "" n
      let branch := match acc.length with
      | 0 =>
        let prefixes := problem₂.prefixes.toArray
        let chars := prefixes.map (λp => Match.mk p.char p.capture ((problem₂.specialize p).solve' n))
        Branch.chars chars
      | 1 =>
        let p := problem.prefixes.toArray.get! 0
        Branch.chars #[Match.mk p.char p.capture (problem₂.solve' n)]
      | _ =>
        Branch.string (Match.mk acc true (problem₂.solve' n))

      Tree.branch branch (Problem.solve' #[otherwise] n)

/-- Solves the problem returning a tree of actions -/
def Problem.solve (problem: Problem Action) : Tree Action :=
  problem.solve' problem.stepsNum
