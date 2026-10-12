import Smt

-- Instantiated RARE rules mention cvc5's internal `@bv` and `@bvsize` operators.

example (x : BitVec 32) : x ^^^ x = 0#32 := by
  smt

example (x : BitVec 32) (h : x < 0#32) : False := by
  smt [h]

example (f : BitVec 32 → Prop) (x : BitVec 32) (h : f (x.smtUDiv 1#32)) : f x := by
  smt [h]
