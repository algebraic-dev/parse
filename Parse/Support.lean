namespace Parse.Support

--| Section of a ByteArray used for a bunch of things
structure SubArray where
  array : ByteArray
  start : Nat
  end_ : Nat
  proof : start ≤ end_ ∧ end_ ≤ array.size

def SubArray.new (array: ByteArray) : SubArray :=
  SubArray.mk array 0 array.size (by simp)

def SubArray.fromString (str: String) : SubArray :=
  SubArray.new (str.toUTF8)

def SubArray.next (sub: SubArray) : SubArray :=
  if h : sub.start + 1 ≤ sub.end_
    then {sub with start := sub.start + 1, proof := ⟨h, sub.proof.right⟩}
    else sub

def SubArray.consume (consume: Nat) (sub: SubArray) : SubArray :=
  if h : sub.start + consume ≤ sub.end_
    then {sub with start := sub.start + consume, proof := ⟨h, sub.proof.right⟩}
    else sub

def SubArray.size (sub: SubArray) : Nat :=
  sub.end_ - sub.start

def SubArray.get (sub: SubArray) (pointer: Fin sub.array.size) : UInt8 :=
  sub.array.get pointer

def SubArray.get! (sub: SubArray) (pointer: Nat) : UInt8 :=
  sub.array.get! pointer

def SubArray.current (sub: SubArray) : UInt8 :=
  sub.array[sub.start]!

def SubArray.isEmpty (sub: SubArray) : Bool :=
  sub.start == sub.end_

inductive State
  | failed
  | succeded
  | paused (next: Nat)
  deriving Repr

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
    then return State.succeded
    else return State.paused matched
