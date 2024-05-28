namespace Parse.Support

set_option linter.all true

/-!
  Support module for the Lean Generator. It is used by the generated code to parse
-/

/-- Section of a ByteArray used for indexing and cutting byte arrays in constant time -/
structure SubArray where
  /-- The internal array -/
  array : ByteArray
  /-- The start of the cut of the byte array -/
  start : Nat
  /-- The end of the cut of the byte array -/
  end_ : Nat
  /-- The proof that the interval is well formed -/
  proof : start ≤ end_ ∧ end_ ≤ array.size

/-- Creates a new SubArray out of a byte array -/
@[inline]
def SubArray.new (array: ByteArray) : SubArray :=
  SubArray.mk array 0 array.size (by simp)

/-- Creates a new SubArray from a String -/
@[inline]
def SubArray.fromString (str: String) : SubArray :=
  SubArray.new (str.toUTF8)

/-- Removes one byte from the beggining of the SubArray -/
@[inline]
def SubArray.next (sub: SubArray) : SubArray :=
  if h : sub.start + 1 ≤ sub.end_
    then {sub with start := sub.start + 1, proof := ⟨h, sub.proof.right⟩}
    else sub

/-- Removes a bunch of bytes from the beggining of the SubArray -/
@[inline]
def SubArray.consume (consume: Nat) (sub: SubArray) : SubArray :=
  if h : sub.start + consume ≤ sub.end_
    then {sub with start := sub.start + consume, proof := ⟨h, sub.proof.right⟩}
    else sub

/-- Gets the size of the subarray -/
@[inline]
def SubArray.size (sub: SubArray) : Nat :=
  sub.end_ - sub.start

/-- Gets an element of the SubArray and panics if it's out of bounds -/
@[inline]
def SubArray.get! (sub: SubArray) (pointer: Nat) : UInt8 :=
  sub.array.get! (pointer + sub.start)

/-- Gets the current byte in the beggining of the SubArray -/
@[inline]
def SubArray.current (sub: SubArray) : UInt8 :=
  sub.array[sub.start]!

/-- Checks if the SubArray is empty -/
@[inline]
def SubArray.isEmpty (sub: SubArray) : Bool :=
  sub.start == sub.end_

/-- Convert a hexadecimal character into a nat -/
@[inline]
def hexCharToNat (char: UInt8) : Nat :=
  if 48 ≤ char ∧ char ≤ 57 then char.toNat - 48
  else if 97 ≤ char ∧ char ≤ 102 then 10 + (char.toNat - 97)
  else if 65 ≤ char ∧ char ≤ 70 then 10 + (char.toNat - 65)
  else 0

/-- State of comparison between strings. it can pause if the input is over and the matcher isnt -/
inductive State
  /-- The match failed because two chars are different -/
  | failed
  /-- The match succeded because the matcher is the prefix of the input -/
  | succeeded
  /-- The match paused after `n` chars because the input is over -/
  | paused (n: Nat)
  deriving Repr

/-- Checks if two strings are the same but with a `pointer` that is used to drop some chars
    from the `matcher`. It is the way it's because its used for incremental comparison-/
def matchStr (matcher: String) (pointer: Nat) (input: SubArray) : State := Id.run do
  let mut matcher := SubArray.fromString matcher
  let mut input := input
  let mut matched := 0

  let max := matcher.size.min input.size

  for i in [:max] do
    if matcher.get! (pointer + i) != input.get! i
      then return State.failed
      else matched := matched + 1

  if matched + pointer == matcher.size
    then return State.succeeded
    else return State.paused matched
