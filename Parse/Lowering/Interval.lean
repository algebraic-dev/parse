/-!
  Definition of ASCII character intervals, useful to compile down to a definition that is the most
  efficient to check if some character is on a range.
-/

namespace Parse.Lowering.Interval

/-- Range of well formed ASCII characters -/
abbrev Range := {range: UInt8 × UInt8 // range.fst ≤ range.snd }

instance : Inhabited Range where
  default := ⟨(0, 0), by decide⟩

/-- Ranges of intervals -/
abbrev Interval := Array Range

/-- Sorts and optimizes the interval to a state that it`s easier to test -/
def Interval.merge (intervals: Interval) : Interval := Id.run do
  let mut merged := #[]
  let intervals := intervals.qsort (·.val.1 < ·.val.1)
  let last : Range := ⟨(0, 0), by decide⟩
  for interval in intervals do
    let currentInt := interval.val
    let lastInt := (merged.back?.getD last).val
    if merged.isEmpty || currentInt.fst > lastInt.snd + 1
      then merged := merged.push interval
      else let last := merged.getD (merged.size-1) last
           let snd : { x : UInt8 // last.val.fst ≤ x } :=
           if h : last.val.snd ≤ interval.val.snd
             then ⟨interval.val.snd, Nat.le_trans last.property h⟩
             else ⟨last.val.snd, last.property⟩
           merged := merged.set! (merged.size - 1) ⟨(last.val.fst, snd.val), snd.property⟩
  return merged

/-- Creates a range that only one char belongs -/
def Range.ofChar (char: Char) : Range :=
  let char := char.toNat.toUInt8
  ⟨(char, char), by simp; exact (Nat.le_of_eq rfl)⟩

def Range.in (range: Range) (char: UInt8) : Bool :=
  range.val.fst ≤ char && char ≤ range.val.snd

/-- Creates an interval from chars -/
def Interval.ofChars (chars: Array Char) :=
  chars.map Range.ofChar
  |> Interval.merge

/-- Checks if a char belongs to an interval -/
def Interval.in (int: Interval) (char: UInt8) : Bool :=
  int.any (Range.in · char)
