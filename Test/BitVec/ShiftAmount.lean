import Smt

-- The shift amount of `bvshl`/`bvlshr`/`bvashr` is the second operand, not an index.

example (x y : BitVec 32) (h : x <<< y = 5#32) : x <<< y = 5#32 := by
  smt [h]

example (x y : BitVec 32) (h : x >>> y = 5#32) : x >>> y = 5#32 := by
  smt [h]

example (x y : BitVec 32) (h : x.sshiftRight' y = 5#32) : x.sshiftRight' y = 5#32 := by
  smt [h]

example (x y z : BitVec 8) (h : x <<< y = z) : z = x <<< y := by
  smt [h]
