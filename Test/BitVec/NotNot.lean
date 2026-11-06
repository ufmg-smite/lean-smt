import Smt

example (f : BitVec 8 → Prop) (x : BitVec 8) (h : f (~~~(~~~x))) : f x := by
  smt [h]

example (f : BitVec 32 → BitVec 32) (x : BitVec 32) : f (~~~(~~~x)) = f x := by
  smt
