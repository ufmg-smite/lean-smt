import Smt

theorem forallExists : ∀ x : Nat, ∃ y : Int, x ≤ y := by
  smt
  intro x
  apply Exists.intro
  case w => exact Int.ofNat x
  case h =>
    induction x with
    | zero => decide
    | succ x _ =>
        simp only [LE.le, Int.le, HSub.hSub, Sub.sub, Int.sub, Neg.neg,
                   Int.neg, Int.negOfNat, HAdd.hAdd, Add.add, Int.add]
        simp only [Int.subNatNat, Nat.sub_self, Int.NonNeg.mk]
