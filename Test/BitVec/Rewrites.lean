import Smt

/-! Goals whose cvc5 proofs use bit-vector RARE rewrite rules (named in the comments). The proof
steps are reconstructed with the theorems in `Smt/Reconstruct/BitVec/Rewrites*.lean`. -/

-- bv-extract-extract
example (x : BitVec 8) : (x.extractLsb 6 2).extractLsb 2 1 = x.extractLsb 4 3 := by smt

-- bv-extract-concat-2
example (x y : BitVec 8) : (y ++ x).extractLsb 10 5 = y.extractLsb 2 0 ++ x.extractLsb 7 5 := by
  smt

-- bv-extract-sign-extend-2
example (x : BitVec 8) : (x.signExtend 12).extractLsb 9 5 = (x.extractLsb 7 5).signExtend 5 := by
  smt

-- bv-extract-not
example (x : BitVec 8) : (~~~x).extractLsb 5 2 = ~~~(x.extractLsb 5 2) := by smt

-- bv-rotate-left-eliminate-1
example (x : BitVec 8) : x.rotateLeft 3 = x.extractLsb 4 0 ++ x.extractLsb 7 5 := by smt

-- bv-rotate-right-eliminate-1
example (x : BitVec 8) : x.rotateRight 3 = x.extractLsb 2 0 ++ x.extractLsb 7 3 := by smt

-- bv-zero-extend-eliminate
example (x : BitVec 8) : x.zeroExtend 12 = 0#4 ++ x := by smt

-- bv-and-simplify-1
example (x : BitVec 8) : ~~~x &&& x = 0#8 := by smt

-- bv-and-simplify-2
example (x : BitVec 8) : x &&& ~~~x = 0#8 := by smt

-- bv-or-simplify-2
example (x : BitVec 8) : x ||| ~~~x = 255#8 := by smt

-- bv-xor-duplicate
example (x : BitVec 8) : x ^^^ x = 0#8 := by smt

-- bv-ugt-eliminate
example (x y : BitVec 8) : (x > y) = (y < x) := by smt

-- bv-redor-eliminate
example (x : BitVec 8) : x.smtRedor = ~~~(x.smtComp 0#8) := by smt

-- bv-udiv-pow2-not-one
example (x : BitVec 8) : x.smtUDiv 4#8 = 0#2 ++ x.extractLsb 7 2 := by smt

-- bv-urem-pow2-not-one
example (x : BitVec 8) : x % 4#8 = 0#6 ++ x.extractLsb 1 0 := by smt

-- bv-extract-mult-leading-bit
example (p q : BitVec 32) : ((3#64 ++ p) * (0#64 ++ q)).extractLsb 95 94 = 0#2 := by smt

-- bv-uaddo-eliminate
example (x y : BitVec 8) :
    (x.uaddOverflow y = true) = (((0#1 ++ x) + (0#1 ++ y)).extractLsb 8 8 = 1#1) := by
  smt

-- bv-nego-eliminate
example (x : BitVec 8) : (x.negOverflow = true) = (x = 128#8) := by smt

-- bv-zero-extend-ult-const-1
example (x : BitVec 8) : (x.zeroExtend 12 < 37#12) = (x < 37#8) := by smt

-- bv-sign-extend-ult-const-1
example (x : BitVec 8) : (x.signExtend 12 < 37#12) = (x < 37#8) := by smt
