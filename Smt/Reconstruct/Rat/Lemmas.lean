/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas, Abdalrhman Mohamed
-/

import Batteries.Data.Rat

import Smt.Reconstruct.Int.Core
import Smt.Reconstruct.Rat.Core

namespace Rat

section le_lt_defs

variable {x y : Rat}

theorem Rat.le_total (a b : Rat) : a ≤ b ∨ b ≤ a := by
  simpa only [← Rat.le_iff_sub_nonneg, Rat.neg_sub] using Rat.nonneg_total (b - a)

theorem Rat.lt_iff_le_not_le (a b : Rat) : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [← Rat.not_le]
  refine Iff.symm ((and_iff_right_of_imp (a := a ≤ b) (b := ¬ b ≤ a)) ?_)
  intro h
  cases Rat.le_total a b with
  | inl hl => exact hl
  | inr hr => exact False.elim (h hr)

theorem Rat.neg_self_add (c : Rat) : -c + c = 0 := by
  simp [Rat.add_def]
  exact Int.add_left_neg _

theorem Rat.le_antisymm {a b : Rat} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rw [Rat.le_iff_sub_nonneg] at hab hba
  rw [Rat.sub_eq_add_neg] at hba
  rw [← Rat.neg_sub, Rat.sub_eq_add_neg] at hab
  have := Rat.nonneg_antisymm hba hab
  have := congrArg (fun x => x + b) this
  simp at this
  rw [Rat.zero_add] at this
  rw [Rat.add_assoc, Rat.neg_self_add] at this
  rw [Rat.add_zero] at this
  exact this

theorem Rat.le_antisymm_iff (a b : Rat) : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun h ↦ ⟨by rw [h]; exact Rat.le_refl, by rw [h]; exact Rat.le_refl⟩, fun ⟨ab, ba⟩ ↦ le_antisymm ab ba⟩

theorem Rat.le_iff_eq_or_lt (a b : Rat) : a ≤ b ↔ a = b ∨ a < b := by
  rw [Rat.le_antisymm_iff, Rat.lt_iff_le_not_le, ← and_or_left]; simp [Classical.em]

theorem lt_iff_sub_pos (a b : Rat) : a < b ↔ 0 < b - a := by
  constructor
  · intro h
    have ⟨le, nle⟩ := (Rat.lt_iff_le_not_le a b).mp h
    have h' := (Rat.le_iff_sub_nonneg a b).mp le
    cases (Rat.le_iff_eq_or_lt 0 (b - a)).mp h' with
    | inl eq =>
        have eq' := Eq.symm eq
        rw [Rat.sub_eq_add_neg] at eq'
        have h'' := Rat.eq_neg_of_add_eq_zero_left eq'
        rw [Rat.neg_neg] at h''
        rw [h''] at h
        have abs := Rat.ne_of_lt h
        exact (False.elim (abs rfl))
    | inr lt => exact lt
  · intro h
    have ⟨le, nle⟩ := (Rat.lt_iff_le_not_le 0 (b - a)).mp h
    have h' := (Rat.le_iff_sub_nonneg a b).mpr le
    cases (Rat.le_iff_eq_or_lt a b).mp h' with
    | inl eq => rw [eq] at h; simp at h; apply False.elim; exact (Bool.eq_not_self (Rat.blt 0 0)).mp h
    | inr lt => exact lt

variable {x y : Rat}

theorem neg_self_add (c : Rat) : -c + c = 0 := by
  simp [Rat.add_def]
  exact Int.add_left_neg _

theorem neg_add (a b : Rat) : -(a + b) = -a - b := by
  rw [Rat.add_def, Rat.sub_def, Rat.neg_normalize, Int.neg_add, Int.sub_eq_add_neg]
  simp

theorem add_sub_add_left_eq_sub (a b c : Rat) : c + a - (c + b) = a - b := by
  rw [ Rat.sub_eq_add_neg,
       Rat.add_assoc c a (-(c + b)),
       Rat.add_comm a (-(c + b)),
       <- Rat.add_assoc c (-(c + b)) a,
       Rat.neg_add,
       Rat.sub_eq_add_neg,
       <- Rat.add_assoc c (-c) (-b),
       Rat.add_neg_self,
       Rat.zero_add,
       Rat.add_comm,
       Rat.sub_eq_add_neg
    ]

theorem add_le_add_left {a b c : Rat} : c + a ≤ c + b ↔ a ≤ b := by
  rw [Rat.le_iff_sub_nonneg, Rat.add_sub_add_left_eq_sub, ← Rat.le_iff_sub_nonneg]

theorem add_lt_add_left {a b c : Rat} : c + a < c + b ↔ a < b := by
  rw [Rat.lt_iff_sub_pos, Rat.add_sub_add_left_eq_sub, ← Rat.lt_iff_sub_pos]

protected theorem le_antisymm (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
    rw [Rat.le_iff_sub_nonneg] at hxy hyx
    rw [Rat.sub_eq_add_neg] at hyx
    rw [← Rat.neg_sub, Rat.sub_eq_add_neg] at hxy
    have this := Rat.eq_neg_of_add_eq_zero_left (Rat.nonneg_antisymm hyx hxy)
    rwa [Rat.neg_neg] at this

protected theorem le_def : x ≤ y ↔ x.num * y.den ≤ y.num * x.den := by
  rw [← num_divInt_den y, ← num_divInt_den x]
  conv => rhs ; simp only [num_divInt_den]
  exact Rat.divInt_le_divInt (mod_cast x.den_pos) (mod_cast y.den_pos)


theorem le_total : x ≤ y ∨ y ≤ x := by
  simp [Rat.le_def]
  omega

theorem lt_iff_le_not_le {a b : Rat} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [← Rat.not_le]
  refine Iff.symm ((and_iff_right_of_imp (a := a ≤ b) (b := ¬ b ≤ a)) ?_)
  intro h
  cases Rat.le_total a b with
  | inl hl => exact hl
  | inr hr => exact False.elim (h hr)

protected theorem lt_iff_le_and_ne : x < y ↔ x ≤ y ∧ x ≠ y := ⟨
  fun h => ⟨Rat.le_of_lt h, Rat.ne_of_lt h⟩,
  fun h => by
    let ⟨h_le, h_ne⟩ := h
    rw [Rat.lt_iff_le_not_le]
    apply And.intro h_le
    intro h_le'
    let _ := Rat.le_antisymm h_le h_le'
    contradiction
⟩

protected theorem lt_def : x < y ↔ x.num * y.den < y.num * x.den := by
  rw [Rat.lt_iff_le_and_ne, Rat.le_def]
  suffices x ≠ y ↔ x.num * y.den ≠ y.num * x.den by
    constructor <;> intro h
    · exact Int.lt_iff_le_and_ne.mpr ⟨h.left, this.mp h.right⟩
    · have tmp := Int.lt_iff_le_and_ne.mp h
      exact ⟨tmp.left, this.mpr tmp.right⟩
  exact Decidable.not_iff_not.mpr Rat.eq_iff_mul_eq_mul

end le_lt_defs

end Rat

private theorem Rat.mul_le_mul_left {c x y : Rat} (hc : c > 0) : (c * x ≤ c * y) = (x ≤ y) := by
  apply propext
  exact
    numDenCasesOn' x fun n₁ d₁ h₁ =>
    numDenCasesOn' y fun n₂ d₂ h₂ => by
      cases c_def : c with
      | mk' nc dc dc_nz _ =>
        rw [<- c_def, <- divInt_self c]
        have foo : (c.den : Int) ≠ (0 : Int) := by rw [c_def]; exact Int.ofNat_ne_zero.mpr dc_nz
        have bar : (d₂ : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr h₂
        have baz : (d₁ : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr h₁
        rw [Rat.divInt_mul_divInt _ _ foo bar, Rat.divInt_mul_divInt _ _ foo baz]
        have c_den_pos : (0 : Int) < c.den := Int.cast_pos fun a => foo (congrArg Nat.cast a)
        have d1_pos : (0 : Int) < d₁ := Int.cast_pos h₁
        have d2_pos : (0 : Int) < d₂ := Int.cast_pos h₂
        have den_pos1 : (0 : Int) < c.den * d₁ := Int.mul_pos c_den_pos d1_pos
        have den_pos2 : (0 : Int) < c.den * d₂ := Int.mul_pos c_den_pos d2_pos
        rw [Rat.divInt_le_divInt den_pos1 den_pos2]
        rw [Rat.divInt_le_divInt d1_pos d2_pos]
        rw [Int.mul_assoc, Int.mul_assoc]
        constructor
        · intro h
          have c_num_pos : 0 < c.num := Rat.num_pos.mpr hc
          have h' := Int.le_of_mul_le_mul_left h c_num_pos
          rw [<- Int.mul_assoc,
              <- Int.mul_assoc,
              Int.mul_comm n₁ c.den,
              Int.mul_comm n₂ c.den,
              Int.mul_assoc,
              Int.mul_assoc] at h'
          exact Int.le_of_mul_le_mul_left h' c_den_pos
        · intro h
          have : 0 ≤ c.num := Rat.num_nonneg.mpr (Rat.le_of_lt hc)
          refine Int.mul_le_mul_of_nonneg_left ?_ this
          rw [<- Int.mul_assoc,
              <- Int.mul_assoc,
              Int.mul_comm n₁ c.den,
              Int.mul_comm n₂ c.den,
              Int.mul_assoc,
              Int.mul_assoc]
          exact Int.mul_le_mul_of_nonneg_left h (Int.ofNat_zero_le c.den)


private theorem Rat.mul_lt_mul_left {c x y : Rat} : 0 < c → ((c * x < c * y) ↔ (x < y)) :=
  numDenCasesOn' x fun n₁ d₁ h₁ =>
    numDenCasesOn' y fun n₂ d₂ h₂ => by
      cases c_def : c with
      | mk' nc dc dc_nz _ =>
        rw [<- c_def, <- divInt_self c]
        have foo : (c.den : Int) ≠ (0 : Int) := by rw [c_def]; exact Int.ofNat_ne_zero.mpr dc_nz
        have bar : (d₂ : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr h₂
        have baz : (d₁ : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr h₁
        rw [Rat.divInt_mul_divInt _ _ foo bar, Rat.divInt_mul_divInt _ _ foo baz]
        have c_den_pos : (0 : Int) < c.den := Int.cast_pos fun a => foo (congrArg Nat.cast a)
        have d1_pos : (0 : Int) < d₁ := Int.cast_pos h₁
        have d2_pos : (0 : Int) < d₂ := Int.cast_pos h₂
        have den_pos1 : (0 : Int) < c.den * d₁ := Int.mul_pos c_den_pos d1_pos
        have den_pos2 : (0 : Int) < c.den * d₂ := Int.mul_pos c_den_pos d2_pos
        /- rw [Rat.divInt_le_divInt den_pos1 den_pos2] -- we want Rat.divInt_lt_divInt -/
        /- rw [Rat.divInt_le_divInt d1_pos d2_pos] -/
        admit

private theorem Rat.mul_eq_zero_left {x y : Rat} : x ≠ 0 → x * y = 0 → y = 0 :=
  numDenCasesOn' x fun nx dx nz_dx =>
    numDenCasesOn' y fun ny dy nz_dy => by
       intros h1 h2
       apply (Rat.mkRat_eq_zero nz_dy).mpr
       have nxn0 := (Rat.mkRat_ne_zero nz_dx).mp h1
       suffices nx * ny = 0
         by have nxy0 := Int.mul_eq_zero.mp this
            cases nxy0 with
            | inl nx0 => exact False.elim (nxn0 nx0)
            | inr ny0 => exact ny0
       have nz_dy' : (dy : Int) ≠ 0 := Int.ofNat_ne_zero.mpr nz_dy
       have nz_dx' : (dx : Int) ≠ 0 := Int.ofNat_ne_zero.mpr nz_dx
       rw [Rat.divInt_mul_divInt nx ny nz_dx' nz_dy'] at h2
       have nz_dxdy : (dx * dy) ≠ 0 := Nat.mul_ne_zero nz_dx nz_dy
       exact (Rat.mkRat_eq_zero nz_dxdy).mp h2

private def uncurry {p₁ p₂ p₃ : Prop} : (p₁ → p₂ → p₃) → (p₁ ∧ p₂) → p₃ := by
  intros h₁ h₂
  have ⟨ht₁, ht₂⟩ := h₂
  exact h₁ ht₁ ht₂

namespace Smt.Reconstruct.Rat

variable {a b c d : Rat}

theorem add_nonneg {a b : Rat} : 0 ≤ a → 0 ≤ b → 0 ≤ a + b :=
  Rat.numDenCasesOn' a fun n₁ d₁ h₁ ↦ Rat.numDenCasesOn' b fun n₂ d₂ h₂ ↦ by
    have d₁0 : 0 < (d₁ : Int) := mod_cast Nat.pos_of_ne_zero h₁
    have d₂0 : 0 < (d₂ : Int) := mod_cast Nat.pos_of_ne_zero h₂
    intro n₁0 n₂0
    rw [Rat.divInt_add_divInt _ _ (Int.ofNat_ne_zero.mpr h₁) (Int.ofNat_ne_zero.mpr h₂)]
    have : (0 : Int) < d₁ * d₂ := by exact Int.mul_pos d₁0 d₂0
    apply (Rat.divInt_nonneg_iff_of_pos_right this).mpr
    apply Int.add_nonneg
    · apply Int.mul_nonneg
      · exact (Rat.divInt_nonneg_iff_of_pos_right d₁0).mp n₁0
      · exact Int.ofNat_zero_le d₂
    · apply Int.mul_nonneg
      · exact (Rat.divInt_nonneg_iff_of_pos_right d₂0).mp n₂0
      · exact Int.ofNat_zero_le d₁

theorem le_trans {a b c : Rat} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [Rat.le_iff_sub_nonneg] at hab hbc
  have := Rat.add_nonneg hab hbc
  rw [Rat.add_comm] at this
  rw [Rat.sub_eq_add_neg] at this
  rw [Rat.add_assoc] at this
  rw [Rat.sub_eq_add_neg] at this
  rw [<- Rat.add_assoc (-b) b (-a)] at this
  rw [Rat.neg_self_add] at this
  rw [Rat.zero_add] at this
  rw [<- Rat.sub_eq_add_neg] at this
  exact (Rat.le_iff_sub_nonneg a c).mpr this

theorem lt_of_le_not_le {a b : Rat} (hab : a ≤ b) (hba : ¬ b ≤ a) : a < b := Rat.lt_iff_le_not_le.mpr ⟨hab, hba⟩

theorem le_of_lt {a b : Rat} (hab : a < b) : a ≤ b := (Rat.lt_iff_le_not_le.1 hab).1

theorem not_le_of_lt {a b : Rat} (hab : a < b) : ¬ b ≤ a := (Rat.lt_iff_le_not_le.1 hab).2

theorem lt_of_lt_of_le {a b : Rat} (hab : a < b) (hbc : b ≤ c) : a < c :=
  lt_of_le_not_le (le_trans (le_of_lt hab) hbc) fun hca ↦ not_le_of_lt hab (le_trans hbc hca)

theorem lt_trans {a b c : Rat} (hab : a < b) (hbc : b < c) : a < c := lt_of_lt_of_le hab (le_of_lt hbc)

theorem lt_of_le_of_lt {a b c : Rat} (hab : a ≤ b) (hbc : b < c) : a < c :=
  lt_of_le_not_le (le_trans hab (le_of_lt hbc)) fun hca ↦ not_le_of_lt hbc (le_trans hca hab)

theorem sum_ub₁ (h₁ : a < b) (h₂ : c < d) : a + c < b + d := by
  have h' : c + a < c + b := Rat.add_lt_add_left.mpr h₁
  have h'' : b + c < b + d := Rat.add_lt_add_left.mpr h₂
  rw [Rat.add_comm, Rat.add_comm c b] at h'
  exact lt_trans h' h''

theorem sum_ub₂ (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d := by
  have h' : c + a < c + b := Rat.add_lt_add_left.mpr h₁
  have h'' : b + c ≤ b + d := Rat.add_le_add_left.mpr h₂
  rw [Rat.add_comm, Rat.add_comm c b] at h'
  exact lt_of_lt_of_le h' h''

theorem sum_ub₃ (h₁ : a < b) (h₂ : c = d) : a + c < b + d := by
  rw [h₂]
  have : d + a < d + b := Rat.add_lt_add_left.mpr h₁
  rw [Rat.add_comm, Rat.add_comm d b] at this
  exact this

theorem sum_ub₄ (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d := by
  have h' : c + a ≤ c + b := Rat.add_le_add_left.mpr h₁
  have h'' : b + c < b + d := Rat.add_lt_add_left.mpr h₂
  rw [Rat.add_comm, Rat.add_comm c b] at h'
  exact lt_of_le_of_lt h' h''

theorem sum_ub₅ (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  have h' : c + a ≤ c + b := Rat.add_le_add_left.mpr h₁
  have h'' : b + c ≤ b + d := Rat.add_le_add_left.mpr h₂
  rw [Rat.add_comm, Rat.add_comm c b] at h'
  exact le_trans h' h''

theorem sum_ub₆ (h₁ : a ≤ b) (h₂ : c = d) : a + c ≤ b + d := by
  rw [h₂, Rat.add_comm, Rat.add_comm b d]
  exact Rat.add_le_add_left.mpr h₁

theorem sum_ub₇ (h₁ : a = b) (h₂ : c < d) : a + c < b + d := by
  rw [h₁, Rat.add_comm b c, Rat.add_comm b d]
  exact sum_ub₃ h₂ rfl

theorem sum_ub₈ (h₁ : a = b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  rw [h₁]
  exact Rat.add_le_add_left.mpr h₂

theorem sum_ub₉ (h₁ : a = b) (h₂ : c = d) : a + c ≤ b + d := by
  rw [h₁, h₂]
  exact Rat.le_refl

theorem neg_lt_neg  : a < b → -a > -b :=
  Rat.numDenCasesOn' a fun na da da_nz =>
    Rat.numDenCasesOn' b fun nb db db_nz => by
      intro h
      simp only [Rat.neg_divInt]
      refine (Rat.lt_iff_sub_pos (Rat.divInt (-nb) ↑db) (Rat.divInt (-na) ↑da)).mpr ?_
      have h' := (Rat.lt_iff_sub_pos (Rat.divInt na da) (Rat.divInt nb db)).mp h
      have foo : (db : Int) ≠ 0 := Int.ofNat_ne_zero.mpr db_nz
      have bar : (da : Int) ≠ 0 := Int.ofNat_ne_zero.mpr da_nz
      rw [Rat.divInt_sub_divInt _ _ foo bar] at h'
      rw [Rat.divInt_sub_divInt _ _ bar foo]
      have foo' : (0 : Int) < da := Int.cast_pos da_nz
      have bar' : (0 : Int) < db := Int.cast_pos db_nz
      have : ((0 : Int) < da * db) := Int.mul_pos foo' bar'
      rw [Rat.divInt_pos_iff_of_pos_right this]
      have : ((0 : Int) < db * da) := Int.mul_pos bar' foo'
      rw [Rat.divInt_pos_iff_of_pos_right this] at h'
      simp
      rw [Int.add_comm, <- Int.sub_eq_add_neg]
      exact h'

theorem neg_le_neg : a ≤ b → -a ≥ -b :=
  Rat.numDenCasesOn' a fun na da da_nz =>
    Rat.numDenCasesOn' b fun nb db db_nz => by
      intro h
      simp only [Rat.neg_divInt]
      refine (Rat.le_iff_sub_nonneg (Rat.divInt (-nb) ↑db) (Rat.divInt (-na) ↑da)).mpr ?_
      have h' := (Rat.le_iff_sub_nonneg (Rat.divInt na da) (Rat.divInt nb db)).mp h
      have foo : (db : Int) ≠ 0 := Int.ofNat_ne_zero.mpr db_nz
      have bar : (da : Int) ≠ 0 := Int.ofNat_ne_zero.mpr da_nz
      rw [Rat.divInt_sub_divInt _ _ foo bar] at h'
      rw [Rat.divInt_sub_divInt _ _ bar foo]
      have foo' : (0 : Int) < da := Int.cast_pos da_nz
      have bar' : (0 : Int) < db := Int.cast_pos db_nz
      have : ((0 : Int) < da * db) := Int.mul_pos foo' bar'
      rw [Rat.divInt_nonneg_iff_of_pos_right this]
      have : ((0 : Int) < db * da) := Int.mul_pos bar' foo'
      rw [Rat.divInt_nonneg_iff_of_pos_right this] at h'
      simp
      rw [Int.add_comm, <- Int.sub_eq_add_neg]
      exact h'

theorem int_tight_ub {i : Int} (h : i < c) : i ≤ c.ceil - 1 := by
  sorry

theorem int_tight_lb {i : Int} (h : i > c) : i ≥ c.floor + 1 := by
  sorry

theorem trichotomy₁ (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b := by
  refine Rat.not_le.mp ?_
  intro abs
  have h := Rat.le_antisymm h₁ abs
  exact h₂ h

theorem trichotomy₂ (h₁ : a ≤ b) (h₂ : a ≥ b) : a = b :=
  Rat.le_antisymm h₁ h₂

theorem trichotomy₃ (h₁ : a ≠ b) (h₂ : a ≤ b) : a < b := by
  exact trichotomy₁ h₂ h₁

theorem trichotomy₄ (h₁ : a ≠ b) (h₂ : a ≥ b) : a > b := by
  exact trichotomy₃ (id (Ne.symm h₁)) h₂

theorem trichotomy₅ (h₁ : a ≥ b) (h₂ : a ≤ b) : a = b := by
  exact Rat.le_antisymm h₂ h₁

theorem trichotomy₆ (h₁ : a ≥ b) (h₂ : a ≠ b) : a > b := by
  exact trichotomy₃ (id (Ne.symm h₂)) h₁

theorem lt_eq_sub_lt_zero : (a < b) = (a - b < 0) := by
  apply propext
  constructor
  · intro h; admit
  · intro h; admit

theorem le_eq_sub_le_zero : (a ≤ b) = (a - b ≤ 0) := by
  apply propext
  constructor
  · intro h
    have h' := (Rat.add_le_add_left (c := -b)).mpr h
    rw [Rat.add_comm, Rat.add_comm (-b) b] at h'
    simp [Rat.add_neg_self, <- Rat.sub_eq_add_neg] at h'
    exact h'
  · intro h
    have h' := (Rat.add_le_add_left (c := b)).mpr h
    rw [Rat.sub_eq_add_neg, Rat.add_comm, Rat.add_assoc, Rat.neg_self_add] at h'
    simp [Rat.add_zero] at h'
    exact h'

theorem eq_eq_sub_eq_zero : (a = b) = (a - b = 0) := by
  apply propext
  constructor
  · intro h; rw [h]; simp
  · intro h; admit

theorem ge_eq_sub_ge_zero : (a ≥ b) = (a - b ≥ 0) := by
  apply propext
  exact Rat.le_iff_sub_nonneg b a

theorem gt_eq_sub_gt_zero : (a > b) = (a - b > 0) := by
  apply propext
  exact Rat.lt_iff_sub_pos b a

theorem lt_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) < 0) = (x - y < 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, Rat.mul_lt_mul_left hc]
  rw [lt_eq_sub_lt_zero, @lt_eq_sub_lt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem lt_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  sorry

theorem le_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) ≤ 0) = (x - y ≤ 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, Rat.mul_le_mul_left hc]
  rw [le_eq_sub_le_zero, @le_eq_sub_le_zero b₁, ← this hc₁, ← this hc₂, h]

theorem le_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem eq_of_sub_eq {c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  apply propext
  apply Iff.intro
  · intro ha
    sorry
  · intro hb
    sorry

theorem ge_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) ≥ 0) = (x - y ≥ 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, ge_iff_le, Rat.mul_le_mul_left hc]
  rw [ge_eq_sub_ge_zero, @ge_eq_sub_ge_zero b₁, ← this hc₁, ← this hc₂, h]

theorem ge_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem gt_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) > 0) = (x - y > 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, gt_iff_lt, Rat.mul_lt_mul_left hc]
  rw [gt_eq_sub_gt_zero, @gt_eq_sub_gt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem gt_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem lt_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) :=
  sorry

theorem lt_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  sorry

theorem le_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem le_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem eq_of_sub_eq_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  sorry

theorem ge_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem ge_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem gt_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem gt_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem lt_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) :=
  sorry

theorem lt_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  sorry

theorem le_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem le_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  sorry

theorem eq_of_sub_eq_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  sorry

theorem ge_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem ge_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  sorry

theorem gt_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem gt_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  sorry

theorem mul_sign₁ (ha : a < 0) (hb : b < 0) : a * b > 0 := by
  sorry

theorem mul_sign₃ (ha : a < 0) (hb : b > 0) : a * b < 0 := by
  sorry

theorem mul_sign₄ (ha : a > 0) (hb : b < 0) : a * b < 0 := by
  sorry

theorem mul_sign₆ (ha : a > 0) (hb : b > 0) : a * b > 0 := by
  sorry

theorem mul_sign₀ (ha : a ≠ 0) : a * a > 0 :=
  sorry

theorem mul_sign₂ (ha : a < 0) (hb : b ≠ 0) : a * b * b < 0 :=
  sorry

theorem mul_sign₅ (ha : a > 0) (hb : b ≠ 0) : a * b * b > 0 :=
  sorry

theorem mul_pos_lt (h : c > 0 ∧ a < b) : c * a < c * b := by
  have ⟨h1, h2⟩ := h
  exact (Rat.mul_lt_mul_left h1).mpr h2

theorem mul_pos_le (h : c > 0 ∧ a ≤ b) : c * a ≤ c * b := by
  have ⟨h1, h2⟩ := h
  exact (Rat.mul_le_mul_left h1).mpr h2

theorem mul_pos_gt (h : c > 0 ∧ a > b) : c * a > c * b :=
  mul_pos_lt h

theorem mul_pos_ge (h : c > 0 ∧ a ≥ b) : c * a ≥ c * b :=
  mul_pos_le h

theorem mul_pos_eq (h : c > 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

theorem mul_neg_lt (h : c < 0 ∧ a < b) : c * a > c * b :=
  sorry

theorem mul_neg_le (h : c < 0 ∧ a ≤ b) : c * a ≥ c * b :=
  sorry

theorem mul_neg_gt (h : c < 0 ∧ a > b) : c * a < c * b :=
  mul_neg_lt h

theorem mul_neg_ge (h : c < 0 ∧ a ≥ b) : c * a ≤ c * b :=
  mul_neg_le h

theorem mul_neg_eq (h : c < 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

theorem mul_tangent_mp_lower (h : x * y ≤ b * x + a * y - a * b)
  : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b :=
  sorry

theorem mul_tangent_mpr_lower (h : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b)
  : x * y ≤ b * x + a * y - a * b :=
  sorry

theorem mul_tangent_lower :
  x * y ≤ b * x + a * y - a * b ↔ x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b :=
  ⟨mul_tangent_mp_lower, mul_tangent_mpr_lower⟩

theorem mul_tangent_lower_eq
  : (x * y ≤ b * x + a * y - a * b) = (x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b) :=
  propext (mul_tangent_lower)

theorem mul_tangent_mp_upper (h : x * y ≥ b * x + a * y - a * b)
  : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b :=
  sorry

theorem mul_tangent_mpr_upper (h : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b)
  : x * y ≥ b * x + a * y - a * b :=
  sorry

theorem mul_tangent_upper
  : x * y ≥ b * x + a * y - a * b ↔ x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b :=
  ⟨mul_tangent_mp_upper, mul_tangent_mpr_upper⟩

theorem mul_tangent_upper_eq
  : (x * y ≥ b * x + a * y - a * b) = (x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b) :=
  propext (mul_tangent_upper)

end Smt.Reconstruct.Rat
