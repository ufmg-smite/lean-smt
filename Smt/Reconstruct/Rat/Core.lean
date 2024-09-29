/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Batteries.Logic
import Batteries.Data.Rat

import Smt.Reconstruct.Int.Core



namespace Rat


section basics

theorem num_divInt_den (q : Rat) : q.num /. q.den = q :=
  divInt_self _

theorem mk'_eq_divInt {n d h c} : (⟨n, d, h, c⟩ : Rat) = n /. d :=
  (num_divInt_den _).symm

theorem divInt_num (q : Rat) : (q.num /. q.den).num = q.num := by
  simp [mkRat, q.den_nz, normalize, Rat.reduced]

theorem divInt_num'
  {n : Int} {d : Nat}
  (nz_d : d ≠ 0 := by omega)
  (reduced : n.natAbs.Coprime d := by assumption)
: (n /. d).num = n := by
  simp [mkRat, nz_d, normalize, reduced]

theorem divInt_den (q : Rat) : (q.num /. q.den).den = q.den := by
  simp [mkRat, q.den_nz, normalize, Rat.reduced]

theorem divInt_den'
  {n : Int} {d : Nat}
  (nz_d : d ≠ 0 := by omega)
  (reduced : n.natAbs.Coprime d := by assumption)
: (n /. d).den = d := by
  simp [mkRat, nz_d, normalize, reduced]

@[elab_as_elim]
def numDenCasesOn.{u} {C : Rat → Sort u}
: ∀ (a : Rat) (_ : ∀ n d, 0 < d → (Int.natAbs n).Coprime d → C (n /. d)), C a
| ⟨n, d, h, c⟩, H => by rw [mk'_eq_divInt]; exact H n d (Nat.pos_of_ne_zero h) c

@[elab_as_elim]
def numDenCasesOn'.{u} {C : Rat → Sort u} (a : Rat)
  (H : ∀ (n : Int) (d : Nat), d ≠ 0 → C (n /. d))
: C a :=
  numDenCasesOn a fun n d h _ => H n d (Nat.pos_iff_ne_zero.mp h)

@[elab_as_elim]
def numDenCasesOn''.{u} {C : Rat → Sort u} (a : Rat)
  (H : ∀ (n : Int) (d : Nat) (nz red), C (mk' n d nz red))
: C a :=
  numDenCasesOn a fun n d h h' ↦ by
    let h_pos := Nat.pos_iff_ne_zero.mp h
    rw [← mk_eq_divInt _ _ h_pos h']
    exact H n d h_pos _

theorem normalize_eq_mk'
  (n : Int) (d : Nat) (h : d ≠ 0) (c : Nat.gcd (Int.natAbs n) d = 1)
: normalize n d h = mk' n d h c :=
  (mk_eq_normalize ..).symm

protected theorem normalize_den_ne_zero
: ∀ {d : Int} {n : Nat}, (h : n ≠ 0) → (normalize d n h).den ≠ 0 := by
  intro d n nz
  simp only [Rat.normalize_eq, ne_eq]
  intro h
  apply nz
  rw [← Nat.zero_mul (d.natAbs.gcd n)]
  apply Nat.div_eq_iff_eq_mul_left _ _ |>.mp
  · assumption
  · exact Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero nz)
  · exact Nat.gcd_dvd_right _ _

protected theorem eq_mkRat : ∀ a : Rat, a = mkRat a.num a.den := fun a => by
  simp [Rat.mkRat_def, a.den_nz, Rat.normalize_eq, a.reduced]

@[simp]
theorem mk'_zero (d) (h : d ≠ 0) (w) : mk' 0 d h w = 0 := by
  congr
  apply Nat.coprime_zero_left d |>.mp w


theorem eq_iff_mul_eq_mul {p q : Rat} : p = q ↔ p.num * q.den = q.num * p.den := by
  conv =>
    lhs
    rw [← num_divInt_den p, ← num_divInt_den q]
  apply Rat.divInt_eq_iff <;>
    · rw [← Int.natCast_zero, Ne, Int.ofNat_inj]
      apply den_nz

end basics



section le_lt_basics

protected theorem not_le {q' : Rat} : ¬q ≤ q' ↔ q' < q := by
  exact (Bool.not_eq_false _).to_iff

protected theorem not_lt {q' : Rat} : ¬q < q' ↔ q' ≤ q := by
  rw [not_congr (Rat.not_le (q := q') (q' := q)) |>.symm]
  simp only [Decidable.not_not]

protected theorem lt_iff_blt {x y : Rat} : x < y ↔ x.blt y := by
  simp only [LT.lt]

protected theorem le_iff_blt {x y : Rat} : x ≤ y ↔ ¬ y.blt x := by
  simp [LE.le]

protected theorem lt_asymm {x y : Rat} : x < y → ¬ y < x := by
  simp [Rat.lt_iff_blt]
  simp [Rat.blt]
  intro h
  cases h with
  | inl h =>
    simp [Int.not_lt_of_lt_rev h.1, Int.not_le.mpr h.1, Int.le_of_lt h.1]
    intro nz_ynum ynum_neg _
    apply ynum_neg
    apply Int.lt_of_le_of_ne h.2
    intro h
    apply nz_ynum
    rw [h]
  | inr h =>
    split at h
    case isTrue xnum_0 =>
      simp [Int.not_lt_of_lt_rev h, xnum_0, h]
    case inr xnum_ne_0 =>
      let ⟨h, h'⟩ := h
      simp [Int.not_lt_of_lt_rev h']
      cases h
      case inl h =>
        simp [h]
        intro _ xnum_pos
        apply h
        apply Int.lt_of_le_of_ne xnum_pos
        intro eq ; apply xnum_ne_0 ; rw [eq]
      case inr h =>
        simp [Int.not_le.mp h |> Int.not_lt_of_lt_rev]
        intro eq
        rw [eq] at h
        contradiction

end le_lt_basics



section add_basics

variable (a b c : Rat)

protected theorem add_comm : a + b = b + a := by
  simp [add_def, Int.add_comm, Int.mul_comm, Nat.mul_comm]

protected theorem add_zero : ∀ a : Rat, a + 0 = a
| ⟨num, den, _h, _h'⟩ => by
  simp [Rat.add_def]
  simp only [Rat.normalize_eq_mkRat, Rat.mk_eq_normalize]

protected theorem zero_add : 0 + a = a :=
  Rat.add_comm a 0 ▸ Rat.add_zero a

protected theorem add_assoc : a + b + c = a + (b + c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
  numDenCasesOn' b fun n₂ d₂ h₂ =>
  numDenCasesOn' c fun n₃ d₃ h₃ => by
    simp only [
      ne_eq, Int.natCast_eq_zero, h₁, not_false_eq_true, h₂,
      Rat.divInt_add_divInt, Int.mul_eq_zero, or_self, h₃
    ]
    rw [Int.mul_assoc, Int.add_mul, Int.add_mul, Int.mul_assoc, Int.add_assoc]
    congr 2
    ac_rfl

end add_basics



section mul_basics

variable {a b : Rat}

protected theorem mul_eq_zero_iff : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · simp only [Rat.mul_def, Rat.normalize_eq_zero]
    intro h
    cases Int.mul_eq_zero.mp h
    · apply Or.inl
      rw [Rat.eq_mkRat a, Rat.mkRat_eq_zero]
      assumption
      exact a.den_nz
    · apply Or.inr
      rw [Rat.eq_mkRat b, Rat.mkRat_eq_zero]
      assumption
      exact b.den_nz
  · intro
    | .inl h => simp only [h, Rat.zero_mul]
    | .inr h => simp only [h, Rat.mul_zero]

protected theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  simp only [not_congr (@Rat.mul_eq_zero_iff a b), not_or, ne_eq]

protected theorem mul_assoc (a b c : Rat) : a + b + c = a + (b + c) :=
  numDenCasesOn' a fun n₁ d₁ _h₁ =>
  numDenCasesOn' b fun n₂ d₂ _h₂ =>
  numDenCasesOn' c fun n₃ d₃ _h₃ => by
    simp only [Rat.divInt_ofNat]
    exact Rat.add_assoc _ _ _

end mul_basics



section num_related

variable {q : Rat}

@[simp]
theorem neg_neg : - -q = q := by
  rw [← Rat.mkRat_self q]
  simp [Rat.neg_mkRat]

@[simp]
theorem num_eq_zero : q.num = 0 ↔ q = 0 := by
  induction q
  constructor
  · rintro rfl
    exact mk'_zero _ _ _
  · exact congr_arg num

theorem num_ne_zero : q.num ≠ 0 ↔ q ≠ 0 := not_congr num_eq_zero

@[simp]
theorem num_nonneg : 0 ≤ q.num ↔ 0 ≤ q := by
  simp [Int.le_iff_lt_or_eq, instLE, Rat.blt, Int.not_lt]
  omega

theorem nonneg_iff_sub_nonpos : 0 ≤ q ↔ -q ≤ 0 := by
  rw [← num_nonneg]
  conv => rhs ; simp [LE.le, Rat.blt]
  omega

theorem nonneg_sub_iff_nonpos : 0 ≤ -q ↔ q ≤ 0 := by
  simp [nonneg_iff_sub_nonpos, Rat.neg_neg]


@[simp]
theorem num_nonpos : q.num ≤ 0 ↔ q ≤ 0 := by
  conv => lhs ; rw [← Int.neg_nonneg]
  simp [Rat.neg_num q ▸ @num_nonneg (-q)]
  conv => rhs ; rw [← nonneg_sub_iff_nonpos]

theorem not_nonpos : ¬ q ≤ 0 ↔ 0 < q := by
  simp [Rat.lt_iff_blt, Rat.blt]
  rw [← num_nonpos]
  exact Int.not_le

@[simp]
theorem num_pos : 0 < q.num ↔ 0 < q := by
  let tmp := not_congr (num_nonpos (q := q))
  rw [Int.not_le] at tmp
  simp [tmp, Rat.not_nonpos]

theorem pos_iff_neg_nonpos : 0 < q ↔ -q < 0 := by
  rw [← num_pos]
  conv => rhs ; simp [Rat.lt_iff_blt] ; unfold Rat.blt ; simp
  constructor <;> intro h
  · apply Or.inl
    exact num_pos.mp h
  · let h : 0 < q := by
      cases h
      case inl h => exact h
      case inr h => exact h.2.2
    apply num_pos.mpr h

@[simp]
theorem num_neg : q.num < 0 ↔ q < 0 := by
  let tmp := @num_pos (-q)
  simp [Rat.neg_num q, Int.lt_neg_of_lt_neg] at tmp
  rw [tmp]
  apply Rat.neg_neg ▸ Rat.pos_iff_neg_nonpos (q := -q)

@[simp]
theorem num_neg_eq_neg_num (q : Rat) : (-q).num = -q.num :=
  rfl

end num_related



section le_lt_extra

variable {x y : Rat}

protected theorem le_refl : x ≤ x := by
  simp [Rat.le_iff_blt, Rat.blt]
  if h : x = 0 then
    simp [h]
    rw [← Rat.num_neg, Rat.zero_num]
    exact Int.lt_irrefl 0
  else
    simp [h]
    rw [← Rat.num_neg, ← Rat.num_pos]
    omega

protected theorem lt_irrefl : ¬ x < x := by
  simp [Rat.not_lt, Rat.le_refl]

protected theorem le_of_lt : x < y → x ≤ y := by
  intro h_lt
  apply Decidable.byContradiction
  intro h
  let _ := Rat.not_le.mp h
  let _ := Rat.lt_asymm h_lt
  contradiction

protected theorem ne_of_lt : x < y → x ≠ y := by
  intro h_lt h_eq
  exact Rat.lt_irrefl (h_eq ▸ h_lt)

end le_lt_extra



section nonneg

variable (x : Rat)

protected theorem nonneg_total : 0 ≤ x ∨ 0 ≤ -x := by
  rw [← num_nonneg (q := -x), ← num_nonneg (q := x)]
  rw [Rat.neg_num, Int.neg_nonneg]
  exact Int.le_total _ _

variable {x}

protected theorem nonneg_antisymm : 0 ≤ x → 0 ≤ -x → x = 0 := by
  rw [← Rat.num_eq_zero, ← Rat.num_nonneg, ← Rat.num_nonneg, Rat.num_neg_eq_neg_num]
  omega

end nonneg



section neg_sub

variable {x y : Rat}

protected theorem neg_sub : -(x - y) = y - x := by
  cases x with | mk' nx dx _ _ =>
  cases y with | mk' ny dy _ _ =>
  simp [Rat.sub_eq_add_neg, Neg.neg]
  simp [Rat.neg, Rat.divInt_ofNat, Rat.add_def, Rat.normalize_eq]
  rw [Nat.mul_comm dx dy]
  constructor
  · rw [← Int.neg_ediv_of_dvd]
    rw [Int.neg_mul, ← Int.sub_eq_add_neg, Int.neg_sub]
    rw [Int.neg_mul, ← Int.sub_eq_add_neg]
    rw [← Int.natAbs_neg, Int.neg_sub]
    · conv => lhs ; arg 1 ; arg 2 ; rw [← Int.natAbs_ofNat (dy * dx)]
      exact Int.gcd_dvd_left
  · rw [Int.neg_mul, ← Int.sub_eq_add_neg]
    rw [Int.neg_mul, ← Int.sub_eq_add_neg]
    rw [← Int.natAbs_neg, Int.neg_sub]

@[simp]
protected theorem sub_self : x - x = 0 :=
  numDenCasesOn' x fun nx dx h_dx => by
    rw [Rat.divInt_sub_divInt _ _ (Int.natCast_ne_zero.mpr h_dx) (Int.natCast_ne_zero.mpr h_dx)]
    simp

protected theorem add_neg_self : x + -x = 0 :=
  Rat.sub_eq_add_neg x x ▸ Rat.sub_self

protected theorem eq_neg_of_add_eq_zero_left : x + y = 0 → x = - y :=
  numDenCasesOn'' x fun nx dx h_dx h_dx_red =>
  numDenCasesOn'' y fun ny dy h_dy h_dy_red => by
    simp only [Rat.neg_divInt, Rat.add_def, Neg.neg]
    simp only [Rat.neg, normalize_eq_zero]
    simp only [eq_iff_mul_eq_mul, ← Int.neg_mul_eq_neg_mul]
    intro h
    apply Int.eq_neg_of_eq_neg
    exact Int.neg_eq_of_add_eq_zero h |>.symm

protected theorem le_iff_sub_nonneg (x y : Rat) : x ≤ y ↔ 0 ≤ y - x :=
  numDenCasesOn'' x fun nx dx h_dx _ =>
  numDenCasesOn'' y fun ny dy h_dy _ => by
    let dy_dx_nz : dy * dx ≠ 0 :=
      Nat.mul_ne_zero h_dy h_dx
    change Rat.blt _ _ = false ↔ _
    unfold Rat.blt
    simp only
      [ Bool.and_eq_true, decide_eq_true_eq, Bool.ite_eq_false_distrib,
        decide_eq_false_iff_not, Rat.not_lt, ite_eq_left_iff,
        not_and, Rat.not_le, ← Rat.num_nonneg ]
    if h : ny < 0 ∧ 0 ≤ nx then
      simp [h]
      simp only [Rat.sub_def, Rat.not_le, normalize_eq, Rat.neg]
      simp [← Rat.num_neg]
      apply Int.ediv_neg'
      · apply Int.sub_neg_of_lt
        apply Int.lt_of_lt_of_le (b := 0)
        · apply Int.mul_neg_of_neg_of_pos h.1
          apply Int.natCast_pos.mpr
          apply Nat.pos_of_ne_zero h_dx
        · apply Int.mul_nonneg h.2
          exact Int.zero_le_natCast
      · apply Int.natCast_pos.mpr
        apply Nat.pos_iff_ne_zero.mpr
        exact Nat.gcd_ne_zero_right dy_dx_nz
    else
      simp [h]
      split
      case isTrue nb_0 =>
        simp [nb_0, Rat.sub_eq_add_neg, Rat.zero_add, Rat.nonneg_sub_iff_nonpos, ← Rat.num_nonpos]
        exact Int.not_lt
      case isFalse nb_nz =>
        simp only [Rat.sub_def, normalize_eq, ← Rat.num_nonneg]
        if ny_pos : 0 < ny then
          simp [ny_pos]
          if h_na : 0 < nx then
            simp [Int.not_le.mpr h_na]
            rw [Int.not_lt]
            rw [← Int.sub_nonneg]
            apply Iff.symm
            apply Int.div_gcd_nonneg_iff_of_nz dy_dx_nz
          else
            let na_nonpos := Int.not_lt.mp h_na
            simp [na_nonpos]
            apply Int.div_gcd_nonneg_iff_of_nz dy_dx_nz |>.mpr
            · apply Int.sub_nonneg_of_le
              apply Int.le_trans (b := 0)
              apply Int.mul_nonpos_of_nonpos_of_nonneg
              · exact Int.not_lt.mp h_na
              · exact Int.natCast_nonneg
              · apply Int.mul_nonneg _ Int.natCast_nonneg
                exact Int.le_of_lt ny_pos
        else
          simp [ny_pos, Int.not_lt, ← Int.sub_nonneg]
          rw [Int.sub_zero]
          rw [Int.sub_zero]
          apply Iff.symm
          apply Int.div_gcd_nonneg_iff_of_nz dy_dx_nz

protected theorem sub_nonneg {a b : Rat} : 0 ≤ a - b ↔ b ≤ a := by
  rw [Rat.le_iff_sub_nonneg b a]

end neg_sub



section divInt

@[simp]
theorem divInt_nonneg_iff_of_pos_right {a b : Int} (hb : 0 < b) : 0 ≤ a /. b ↔ 0 ≤ a := by
  cases hab : a /. b with | mk' n d hd hnd =>
  rw [mk'_eq_divInt, divInt_eq_iff (Int.ne_of_lt hb).symm (mod_cast hd)] at hab
  rw [
    ← Rat.num_nonneg, ← Int.mul_nonneg_iff_of_pos_right hb, ← hab,
    Int.mul_nonneg_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero hd),
  ]

protected theorem divInt_le_divInt
  {a b c d : Int} (b0 : 0 < b) (d0 : 0 < d)
: a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  rw [Rat.le_iff_sub_nonneg, ← Int.sub_nonneg]
  simp [Rat.sub_eq_add_neg, Rat.neg_divInt, Int.ne_of_gt b0, Int.ne_of_gt d0, Int.mul_pos d0 b0]
  rw [Rat.divInt_add_divInt]
  simp [Rat.divInt_nonneg_iff_of_pos_right (Int.mul_pos d0 b0)]
  rw [← Int.sub_nonneg (a := c * b)]
  rw [Int.neg_mul, ← Int.sub_eq_add_neg]
  · apply Int.lt_iff_le_and_ne.mp d0 |>.2 |>.symm
  · apply Int.lt_iff_le_and_ne.mp b0 |>.2 |>.symm

end divInt

end Rat
