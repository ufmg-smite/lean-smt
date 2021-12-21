import Smt

theorem neg (x : Int) : - -x = x := by
  smt
  induction x with
  | ofNat n   => induction n <;> simp only [Neg.neg, Int.neg, Int.negOfNat]
  | negSucc n => simp only [Neg.neg, Int.neg, Int.negOfNat]
