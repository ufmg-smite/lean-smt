import Smt.Tactic.Concretize

def BitVec (w : Nat) := Fin (2^w)

protected def BitVec.zero (w : Nat) : BitVec w :=
  ⟨0, Nat.pos_pow_of_pos _ <| by decide⟩

instance : Inhabited (BitVec w) := ⟨BitVec.zero w⟩

opaque BitVec.xor {w : Nat} : BitVec w → BitVec w → BitVec w

def polyAdd {w : Nat} : BitVec w → BitVec w → BitVec w :=
  BitVec.xor
def polyDouble {w : Nat} (x : BitVec w) : BitVec w :=
  polyAdd x x

example (x y : BitVec 2) : polyDouble (polyAdd x y) = polyDouble (polyAdd y x) := by
  concretize [polyDouble, polyAdd]
  trace_state
  sorry
