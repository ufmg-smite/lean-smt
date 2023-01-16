import Std.Data.Int.Lemmas
import Std.Data.Rat.Basic
import Mathlib.Data.Rat.Order

theorem unwrapDecideFalse {p : Prop} [inst : Decidable p] : decide p = false → ¬ p := by
  intros h
  unfold decide at h
  cases inst with
  | isFalse h' => exact h'
  | isTrue _   => simp at h

theorem unwrapDecideTrue {p : Prop} [inst : Decidable p] : decide p = true → p := by
  intros h
  unfold decide at h
  cases inst with
  | isFalse _ => simp at h
  | isTrue h' => exact h'

theorem wrapDecideTrue {p : Prop} [inst : Decidable p] : p → decide p = true := by
  intros h
  unfold decide
  cases inst with
  | isFalse h' => exact absurd h h'
  | isTrue h' => simp

theorem wrapDecideFalse {p : Prop} [inst : Decidable p] : ¬ p → decide p = false := by
  intros h
  unfold decide
  cases inst with
  | isFalse _ => simp
  | isTrue hp => exact absurd hp h

theorem castLE : ∀ {a b : Int}, a ≤ b → Rat.ofInt a ≤ Rat.ofInt b := by
  intros a b h
  have bNumerator: (Rat.ofInt b).num = b := Rat.ofInt_num
  show Rat.blt b a = false
  unfold Rat.blt
  split_ifs with h₁ h₂ h₃
  { 
    simp at h₁
    have ⟨h₁f, h₁s⟩ := h₁
    have bNeg : b < 0 := unwrapDecideTrue h₁f
    have aNotNeg : 0 ≤ a := unwrapDecideTrue h₁s
    have abs : b < a := lt_of_lt_of_le bNeg aNotNeg
    exact (not_le_of_gt abs) h
  }
  {
    have h₂' := symm h₂
    have bEq0 : 0 = b := Eq.trans h₂' bNumerator
    rw [← bEq0] at h
    simp
    have abs := not_lt_of_ge h
    exact wrapDecideFalse abs
  }
  { exact rfl }
  simp
  exact h

theorem div_add_one_ge_add_one_div : ∀ {n d : Nat},
  - Int.ofNat ((n/d + 1) * d) + d ≤ -(1 + n) / d * d + d :=
    by intros n d
       simp
       rw [← Int.neg_add]
       rw [← Int.neg_mul]
       apply flip mul_le_mul_of_nonneg_right (by simp)
       norm_cast
       cases d with
       | zero =>
           simp
           show -1 ≤ Int.ediv (Int.negSucc (Nat.succ n)) 0
           unfold Int.ediv
           simp
       | succ d' => 
           simp
           show Int.negSucc (n / Nat.succ d') ≤ Int.ediv (Int.negSucc n) (Nat.succ d')
           unfold Int.ediv
           simp

theorem floorLtImplies : ∀ {c : Rat} {i : Int}, Rat.floor c < i → Rat.floor c + 1 ≤ i := by
  intros c i h
  exact (Int.lt_iff_add_one_le (Rat.floor c) i).mp h

theorem floorPlusOneGt : ∀ (c : Rat), c < Rat.ofInt (Rat.floor c + 1) := by
  intro c
  show Rat.blt c (Rat.ofInt (Rat.floor c + 1))
  unfold Rat.blt
  split_ifs with h₁ h₂ h₃
  { exact rfl }
  {
    unfold Rat.floor
    apply wrapDecideTrue
    rw [h₂]
    simp
    split_ifs with h₄
    { simp }
    { rw [Int.zero_ediv c.den]; simp  }
  }
  {
    simp at *
    have ⟨h₄, h₅⟩ := h₃
    unfold Rat.floor at h₅
    split_ifs at h₅ with h₆
    {
      simp at h₅
      norm_cast at h₅
      have h₄' := add_lt_add_right h₄ 1
      have abs := lt_of_lt_of_le h₄' h₅
      simp at abs
    }
    norm_cast at h₅
    simp at h₅ 
    have blah : 0 ≤ c.num / c.den := Int.ediv_nonneg (le_of_lt h₄) (by simp)
    have bleh := Int.add_le_add_right blah 1
    have blih := le_trans bleh h₅
    simp at blih
  }
  simp at *
  unfold Rat.floor
  split_ifs with h₄
  { rw [h₄]; norm_cast; simp }
  norm_cast
  simp
  cases c.num with
  | ofNat num'   =>
    simp
    norm_cast
    suffices c.den * (num' / c.den) + num' % c.den < (num' / c.den + 1) * c.den 
      by rw [Nat.div_add_mod num' c.den] at this; exact this
    rw [Nat.right_distrib, Nat.mul_comm]
    apply add_lt_add_left
    simp
    apply Nat.mod_lt
    exact (Nat.zero_lt_of_ne_zero c.den_nz)
  | negSucc num' =>
    show Int.negSucc num' + 1 ≤ (Int.negSucc num' / c.den + 1) * c.den
    rw [Int.negSucc_coe num', Int.ofNat_add, Int.add_mul]
    simp
    rw [← Int.neg_add]
    suffices - Int.ofNat (c.den * (num' / c.den) + num' % c.den) ≤ -(1 + num') / c.den * c.den + c.den
      by rw [Nat.div_add_mod num' c.den] at this; exact this
    have tighter_bound := @div_add_one_ge_add_one_div num' c.den
    apply flip le_trans tighter_bound
    norm_cast
    simp
    rw [Int.add_mul, Int.mul_comm, Int.add_comm, ← Int.add_assoc]
    simp
    have coe_nz (i : Nat) : i ≠ 0 → Int.ofNat i ≠ 0 := by simp
    exact Int.emod_nonneg num' (coe_nz c.den c.den_nz)

theorem intTightUb : ∀ {i : Int} {c : Rat}, Rat.ofInt i < c → i ≤ Rat.floor c := by
  intros i c h
  cases lt_trichotomy i (Rat.floor c) with
  | inl iltc => exact le_of_lt iltc
  | inr h'   => cases h' with
                | inl ieqc => exact le_of_eq ieqc
                | inr igtc =>
                  have bloh := castLE (floorLtImplies igtc)
                  have bluh := floorPlusOneGt c
                  have h' := lt_of_lt_of_le bluh bloh
                  exact absurd h (lt_asymm h')

theorem intTightLb : ∀ {i : Int} {c : Rat}, i > c → i ≥ Rat.ceil c := sorry
