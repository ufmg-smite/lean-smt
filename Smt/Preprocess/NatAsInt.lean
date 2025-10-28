theorem Nat.forall_as_int (P : Nat → Prop) : (∀ x : Nat, P x) ↔ (∀ x : Int, x ≥ 0 → P x.toNat) := by
  constructor
  · intro h x x_nonneg
    let x_nat : Nat := x.toNat
    have h_nat : x = x_nat := by
      exact Int.eq_natCast_toNat.mpr x_nonneg
    rw [h_nat]
    exact h x_nat
  · intro h x
    let x_int : Int := x
    apply h x_int
    exact Int.ofNat_zero_le x

theorem Nat.exists_as_int (P : Nat → Prop) : (∃ x : Nat, P x) ↔ (∃ x : Int, x ≥ 0 ∧ (x ≥ 0 → P x.toNat)) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    exists x
    exact if_false_right.mp fun a => hx
  · intro h
    obtain ⟨x, hx⟩ := h
    let x_nat : Nat := x.toNat
    have h_nat : x = x_nat := by
      refine Int.eq_natCast_toNat.mpr ?_
      exact hx.1
    exists x_nat
    unfold x_nat
    have : x ≥ 0 := hx.1
    exact hx.2 this

def Int.natSub (x y : Int) :=
  if x ≥ y then x - y else 0

theorem Int.natCast_sub2 (x y : Nat) : (x - y : Nat) = Int.natSub x y := by
  rw [Int.natSub]
  split <;> rename_i h
  · rw [Int.natCast_sub]
    exact Int.ofNat_le.mp h
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_succ_le (Int.ofNat_lt.mp (Int.not_le.mp h))), Int.natCast_zero]

theorem Int.ofNat_eq (x y : Nat) : (x = y) = ((x : Int) = (y : Int)) := by
  simp only [Int.ofNat_inj]

theorem Int.ofNat_le2 (x y : Nat) : (x ≤ y) = ((x : Int) ≤ (y : Int)) := by
  simp only [Int.ofNat_le]

theorem Int.ofNat_lt2 (x y : Nat) : (x < y) = ((x : Int) < (y : Int)) := by
  simp only [Int.ofNat_lt]

theorem Int.ofNat_ge (x y : Nat) : (x ≥ y) = ((x : Int) ≥ (y : Int)) := by
  simp only [ge_iff_le, Int.ofNat_le]

theorem Int.ofNat_gt (x y : Nat) : (x > y) = ((x : Int) > (y : Int)) := by
  simp only [gt_iff_lt, Int.ofNat_lt]

theorem Int.ofNat_ne (x y : Nat) : x ≠ y ↔ ((x : Int) ≠ (y : Int)) := by
  rw [← Decidable.not_iff_not]
  rw [Decidable.not_not, Decidable.not_not]
  rw [Int.ofNat_inj]

theorem doubleCast (p : Nat → Prop) (w : Nat) : p w = p (w : Int).toNat := by
  rw [← congrArg p (Int.toNat_natCast w)]
