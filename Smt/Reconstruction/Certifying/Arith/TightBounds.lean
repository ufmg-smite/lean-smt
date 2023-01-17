import Std.Data.Int.Lemmas
import Std.Data.Rat.Basic
import Mathlib.Data.Rat.Order

import Smt.Reconstruction.Certifying.Boolean


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
       rw [← Int.neg_add, ← Int.neg_mul]
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

theorem ceilGtImplies : ∀ {c : Rat} {i : Int}, i < Rat.ceil c → i ≤ Rat.ceil c - 1 := by
  intros c i h
  exact Int.le_sub_one_of_lt h

def q : Rat := { num := 0, den := 1, reduced := by simp, den_nz := by simp }
#eval Rat.ofInt (Rat.ceil q - 1)


theorem ceilSubOneLt : ∀ (c : Rat), Rat.ofInt (Rat.ceil c - 1) < c := by
  intro c
  show Rat.blt (Rat.ofInt (Rat.ceil c - 1)) c
  unfold Rat.blt
  split_ifs with h₁ h₂ h₃
  { exact rfl }
  {
    apply wrapDecideTrue
    norm_cast at h₂
    unfold Rat.ceil at h₂
    split_ifs at h₂ with h₃
    { rw [Int.eq_of_sub_eq_zero h₂]; simp  }
    simp at h₂
    have c_red := c.reduced
    cases lt_trichotomy 0 c.num with
    | inl num_pos => exact num_pos
    | inr h'      => cases h' with
                     | inl num_zero => rw [Eq.symm num_zero] at c_red
                                       simp at c_red
                                       exact absurd c_red h₃
                     | inr num_neg  =>
                         have den_pos : 0 < (c.den : Int) := by
                           rw [← Int.ofNat_eq_cast]
                           simp
                           exact Nat.pos_of_ne_zero c.den_nz
                         have rat_neg : c.num / c.den < 0 := Int.ediv_neg' num_neg den_pos
                         rw [h₂] at rat_neg
                         simp at rat_neg
     
  }
  {
    simp at h₃
    have ⟨ceil_pos, num_not_pos⟩ := h₃
    clear h₃
    unfold Rat.ceil at ceil_pos
    split_ifs at ceil_pos with c_den_one
    {
      norm_cast at ceil_pos
      have ceil_pos' := Int.add_lt_add_right ceil_pos 1
      simp at ceil_pos'
      have abs := lt_of_lt_of_le ceil_pos' num_not_pos
      simp at abs
    }
    simp at ceil_pos
    have num_ne_zero : c.num ≠ 0 := by
      apply Classical.byContradiction
      intro abs
      have abs' := notNotElim abs
      have c_red := c.reduced
      rw [abs'] at c_red
      simp at c_red
      exact absurd c_red c_den_one
    have num_neg : c.num < 0 := lt_of_le_of_ne num_not_pos num_ne_zero
    have den_pos : 0 < (c.den : Int) := by
      rw [← Int.ofNat_eq_cast]
      simp
      exact Nat.pos_of_ne_zero c.den_nz
    have rat_neg := Int.ediv_neg' num_neg den_pos
    have abs := lt_trans ceil_pos rat_neg
    simp at abs
  }
  simp at *
  norm_cast
  simp
  unfold Rat.ceil
  split_ifs with h'
  { rw [h']; simp }
  simp
  norm_cast
  cases num'_def: c.num with
  | ofNat num'   =>
      simp
      norm_cast
      suffices num' / c.den * c.den < c.den * (num' / c.den) + num' % c.den
        by rw [Nat.div_add_mod num' c.den] at this; exact this
      rw [Nat.mul_comm]
      simp
      apply Classical.byContradiction
      intro abs
      simp at abs
      have blah := Nat.dvd_of_mod_eq_zero abs
      have c_red := c.reduced
      have bleh := Nat.gcd_eq_left_iff_dvd.mp blah
      unfold Nat.coprime at c_red
      rw [Nat.gcd_comm] at c_red
      rw [num'_def] at c_red
      simp at c_red
      rw [bleh] at c_red
      exact absurd c_red h'
  | negSucc num' =>
      show Int.ediv (Int.negSucc num') c.den * c.den < Int.negSucc num'
      unfold Int.ediv
      cases den_def: c.den with
      | zero => exact absurd den_def c.den_nz
      | succ den' =>
          simp
          norm_cast
          rw [← den_def]
          have blah : den' + 1 = c.den := symm den_def
          rw [blah]
          rw [Int.negSucc_coe, Int.negSucc_coe, Int.ofNat_add, Int.ofNat_add]
          rw [Int.neg_add]
          rw [Int.add_mul]
          simp
          suffices -(num' / c.den * c.den : Int) + (-c.den) + Int.ofNat ((c.den * (num' / c.den) + num' % c.den)) < -1
            by rw [Nat.div_add_mod num' c.den] at this; exact this
          simp
          rw [Int.mul_comm]
          rw [← Int.add_assoc]
          rw [Int.add_comm (-(c.den * (num' / c.den))) (-c.den)]
          rw [Int.add_assoc]
          rw [Int.add_assoc]
          simp
          norm_cast
          admit

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
    have ⟨num_pos, h₅⟩ := h₃
    unfold Rat.floor at h₅
    split_ifs at h₅ with h₆
    {
      simp at h₅
      norm_cast at h₅
      have h₄' := add_lt_add_right num_pos 1
      have abs := lt_of_lt_of_le h₄' h₅
      simp at abs
    }
    norm_cast at h₅
    simp at h₅ 
    have rat_nonneg : 0 ≤ c.num / c.den := Int.ediv_nonneg (le_of_lt num_pos) (by simp)
    have rat_gt_one := Int.add_le_add_right rat_nonneg 1
    have abs := le_trans rat_gt_one h₅
    simp at abs
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
                  have coe_igtc := castLE (floorLtImplies igtc)
                  have c_lt := floorPlusOneGt c
                  have h' := lt_of_lt_of_le c_lt coe_igtc

                  exact absurd h (lt_asymm h')

theorem intTightLb : ∀ {i : Int} {c : Rat}, i > c → i ≥ Rat.ceil c := by
  intros i c h
  cases lt_trichotomy i (Rat.ceil c) with
  | inl iltc =>
    have coe_iltc := castLE (ceilGtImplies iltc)
    have c_gt := ceilSubOneLt c
    have h' := lt_of_le_of_lt coe_iltc c_gt
    exact absurd h (lt_asymm h')
  | inr h'   => cases h' with
                | inl ieqc => exact le_of_eq (Eq.symm ieqc)
                | inr igtc => exact le_of_lt igtc
