import Smt.Tactic.Concretize

def polyAdd {w : Nat} : BitVec w → BitVec w → BitVec w :=
  BitVec.xor
def polyDouble {w : Nat} (x : BitVec w) : BitVec w :=
  polyAdd x x

example (x y : BitVec 2) : polyDouble (polyAdd x y) = polyDouble (polyAdd y x) := by
  concretize [polyDouble, polyAdd]
  trace_state
  sorry
