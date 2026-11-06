import Smt

-- `bvand`/`bvor`/`bvxor` must be rebuilt as `&&&`/`|||`/`^^^` so that the
-- commutativity, associativity and absorption instances used by ACI_NORM and
-- ABSORB apply.

example (x y : BitVec 32) : x &&& y = y &&& x := by
  smt

example (x y : BitVec 32) : x ||| y = y ||| x := by
  smt

example (x y : BitVec 32) : x ^^^ y = y ^^^ x := by
  smt

example (x y z : BitVec 16) : (x &&& y) &&& z = x &&& (y &&& z) := by
  smt

example (x y z : BitVec 16) : (x ||| y) ||| z = z ||| (y ||| x) := by
  smt

example (f : BitVec 8 → Prop) (x y : BitVec 8) (h : f (x &&& (y &&& 0#8))) : f 0#8 := by
  smt [h]

example (f : BitVec 8 → Prop) (x y : BitVec 8) (h : f (x ||| (y ||| 255#8))) : f 255#8 := by
  smt [h]
