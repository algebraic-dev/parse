/-!
  Description of Intervals of ASCII characters to optimize the generate code
-/

namespace Parse.Interval

abbrev Range :=  {range: UInt8 × UInt8 // range.fst ≤ range.snd }

instance : Inhabited Range where
  default := ⟨(0, 0), by decide⟩

abbrev Interval := Array Range

def Range.fromChar (char: Char) : Range :=
  let char := char.toNat.toUInt8
  ⟨(char, char), by simp; exact (Nat.le_of_eq rfl)⟩

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

/-- Test if some Uint8 is in the interval -/
def Interval.in (int: Interval) (c: UInt8) : Bool :=
  int.any (λ i => i.val.fst ≤ c && c ≤ i.val.snd)

def Interval.fromChars (chars: Array Char) :=
  chars.map Range.fromChar
  |> Interval.merge
