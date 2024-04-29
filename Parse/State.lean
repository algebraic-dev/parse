/-!
  Library for internal parsing usage
-/

namespace Parse.State

open Lean

def Span := Nat × Nat
deriving instance Inhabited for Span

inductive StringMatch
  | succeded
  | failed
  | paused
  deriving Repr

def strMatch (pointer: Nat) (toMatch: String) (input: Substring) : StringMatch × Nat := Id.run do
  let mut toMatch := toMatch.toSubstring.drop pointer
  let mut input := input

  let minSize := Nat.min toMatch.bsize input.bsize

  let mut used := 0

  for i in [:minSize] do
    used := i + 1
    if toMatch.get (String.Pos.mk i) != input.get (String.Pos.mk i)
      then return (StringMatch.failed, 0)

  if toMatch.bsize != used
    then (StringMatch.paused, used)
    else (StringMatch.succeded, 0)
