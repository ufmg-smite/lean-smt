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

theorem neg_one_mod : ∀ {i : Nat}, Int.emod (-1) i = i - 1 := by
  intro i
  unfold Int.emod
  have neg_one_def : -1 = Int.negSucc 0 := rfl
  rw [neg_one_def]
  simp
  unfold Int.subNatNat
  cases i with
  | zero => simp
  | succ x => cases x with
              | zero => simp
              | succ y => simp; 

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
          rw [Int.negSucc_coe] at num'_def
          rw [Int.ofNat_add] at num'_def
          rw [Int.neg_add] at num'_def
          simp at num'_def
          have h'' : c.num + 1 = -num' + -1 + 1 := congrArg (· + 1) num'_def
          simp at h''
          have hh : -(c.num + 1) = -(-num') := congrArg Int.neg h''
          simp at hh
          rw [← hh]
          cases lt_trichotomy ((-1 + -c.num) % c.den) (c.den - 1) with
          | inl l₁ => 
            have l₁' := add_lt_add_right l₁ 1
            simp at l₁'
            exact l₁'
          | inr h₄ => cases h₄ with
                      | inl l₂ =>
                          apply False.elim
                          have c_red := c.reduced
                          -- have l₂' : Int.emod (-1 + -c.num) c.den = c.den - 1 := l₂
                          -- unfold Int.emod at l₂'
                          rw [hh] at l₂
                          have l₂' := congrArg (· + 1) l₂
                          simp at l₂'
                          have l₂'' := congrArg (fun x => Int.emod x c.den) l₂'
                          simp at l₂''

                          norm_cast at l₂''
                          have l₂3 : Int.emod ((Int.emod num' c.den) + 1) c.den = c.den % (c.den : Int) := l₂''
                          have den_gt_one : 1 < (c.den : Int) := by
                            cases den_def2: c.den with
                            | zero => exact absurd den_def2 c.den_nz
                            | succ x => cases x with
                                        | zero => exact absurd den_def2 h'
                                        | succ y => simp
                          have z : Int.emod 1 c.den = 1 := Int.emod_eq_of_lt (by simp) den_gt_one
                          rw [← z] at l₂3
                          rw [Int.emod_self] at l₂3
                          have l₂3' : ((num' : Int) % c.den + (1 : Int) % c.den) % c.den = 0 := l₂3

                          rw [← Int.add_emod num' 1 c.den] at l₂3'

                          have bleh := Int.dvd_of_emod_eq_zero l₂3'
                          have num'_def' : -c.num = -(-num' + -1) := congrArg Int.neg num'_def
                          rw [Int.neg_add] at num'_def'
                          simp at num'_def'
                          rw [← num'_def'] at bleh
                          have y := Int.dvd_neg.mp bleh
                          unfold Nat.coprime at c_red
                          have y' := Int.dvd_natAbs.mpr y
                          norm_cast at y'
                          have blih := Nat.gcd_eq_right_iff_dvd.mp y'
                          have blih' := Eq.symm blih
                          have abs := Eq.trans blih' c_red
                          exact h' abs
                      | inr l₃ =>
                          have l₃' := Int.le_of_sub_one_lt l₃
                          have den_pos : 0 < (c.den : Int) := by
                            rw [← Int.ofNat_eq_cast]
                            simp
                            exact Nat.pos_of_ne_zero c.den_nz
                          have abs := Int.emod_lt_of_pos (-1 + -c.num) den_pos
                          have abs' := lt_of_lt_of_le abs l₃'
                          simp at abs'

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
