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

theorem le_of_not_le {a b : Rat} : ¬ a ≤ b → b ≤ a := (Rat.le_total a b).resolve_left

theorem lt_iff_le_not_le (a b : Rat) : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [← Rat.not_le]
  refine Iff.symm ((and_iff_right_of_imp (a := a ≤ b) (b := ¬ b ≤ a)) ?_)
  intro h
  cases le_total a b with
  | inl hl => exact hl
  | inr hr => exact False.elim (h hr)

theorem neg_self_add (c : Rat) : -c + c = 0 := by
  simp only [add_def, neg_num, Int.neg_mul, neg_den, Int.add_left_neg, normalize_zero]

theorem le_antisymm {a b : Rat} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rw [Rat.le_iff_sub_nonneg] at hab hba
  rw [Rat.sub_eq_add_neg] at hba
  rw [← Rat.neg_sub, Rat.sub_eq_add_neg] at hab
  have := Rat.nonneg_antisymm _ hba hab
  have := congrArg (fun x => x + b) this
  simp at this
  rw [Rat.add_assoc, Rat.neg_self_add] at this
  rw [Rat.add_zero] at this
  exact this

theorem le_antisymm_iff (a b : Rat) : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun h ↦ ⟨by rw [h]; exact Rat.le_refl _, by rw [h]; exact Rat.le_refl _⟩, fun ⟨ab, ba⟩ ↦ Rat.le_antisymm ab ba⟩

theorem le_iff_eq_or_lt (a b : Rat) : a ≤ b ↔ a = b ∨ a < b := by
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
        have h'' := Rat.eq_neg_of_add_eq_zero_left _ _ eq'
        rw [Rat.neg_neg] at h''
        rw [h''] at h
        have abs := Rat.ne_of_lt _ _ h
        exact (False.elim (abs rfl))
    | inr lt => exact lt
  · intro h
    have ⟨le, nle⟩ := (Rat.lt_iff_le_not_le 0 (b - a)).mp h
    have h' := (Rat.le_iff_sub_nonneg a b).mpr le
    cases (Rat.le_iff_eq_or_lt a b).mp h' with
    | inl eq => rw [eq] at h; simp at h; apply False.elim; exact (Bool.eq_not_self (Rat.blt 0 0)).mp h
    | inr lt => exact lt

protected theorem divInt_lt_divInt
  {a b c d : Int} (b0 : 0 < b) (d0 : 0 < d)
: a /. b < c /. d ↔ a * d < c * b := by
  rw [Rat.lt_iff_sub_pos, ← Int.sub_pos]
  simp only [Rat.sub_eq_add_neg, Rat.neg_divInt]
  rw [Rat.divInt_add_divInt]
  simp only [Int.neg_mul, Rat.divInt_pos_iff_of_pos_right (Int.mul_pos d0 b0), Int.sub_pos]
  rw [← Int.sub_pos (a := c * b)]
  rw [← Int.sub_eq_add_neg]
  · exact Ne.symm (Int.ne_of_lt d0)
  · exact Ne.symm (Int.ne_of_lt b0)

variable {x y : Rat}

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
    ]

theorem add_le_add_left {a b c : Rat} : c + a ≤ c + b ↔ a ≤ b := by
  rw [Rat.le_iff_sub_nonneg, Rat.add_sub_add_left_eq_sub, ← Rat.le_iff_sub_nonneg]

theorem add_lt_add_left {a b c : Rat} : c + a < c + b ↔ a < b := by
  rw [Rat.lt_iff_sub_pos, Rat.add_sub_add_left_eq_sub, ← Rat.lt_iff_sub_pos]

protected theorem le_def : x ≤ y ↔ x.num * y.den ≤ y.num * x.den := by
  rw [← num_divInt_den y, ← num_divInt_den x]
  conv => rhs ; simp only [num_divInt_den]
  exact Rat.divInt_le_divInt (mod_cast x.den_pos) (mod_cast y.den_pos)

protected theorem lt_iff_le_and_ne : x < y ↔ x ≤ y ∧ x ≠ y := ⟨
  fun h => ⟨Rat.le_of_lt _ _ h, Rat.ne_of_lt _ _ h⟩,
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

theorem floor_le_self (r : Rat) : r.floor ≤ r := Rat.le_floor.mp (Int.le_refl r.floor)

theorem self_le_floor_add_one (r : Rat) : r < ↑(r.floor + 1) := by
  sorry

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
        have c_den_pos : (0 : Int) < c.den := Int.cast_pos' fun a => foo (congrArg Nat.cast a)
        have d1_pos : (0 : Int) < d₁ := Int.cast_pos' h₁
        have d2_pos : (0 : Int) < d₂ := Int.cast_pos' h₂
        have den_pos1 : (0 : Int) < c.den * d₁ := Int.mul_pos c_den_pos d1_pos
        have den_pos2 : (0 : Int) < c.den * d₂ := Int.mul_pos c_den_pos d2_pos
        rw [Rat.divInt_le_divInt den_pos1 den_pos2]
        rw [Rat.divInt_le_divInt d1_pos d2_pos]
        rw [Int.mul_assoc, Int.mul_assoc]
        constructor
        · intro h
          have c_num_pos : 0 < c.num := (Rat.num_pos c).mpr hc
          have h' := Int.le_of_mul_le_mul_left h c_num_pos
          rw [<- Int.mul_assoc,
              <- Int.mul_assoc,
              Int.mul_comm n₁ c.den,
              Int.mul_comm n₂ c.den,
              Int.mul_assoc,
              Int.mul_assoc] at h'
          exact Int.le_of_mul_le_mul_left h' c_den_pos
        · intro h
          have : 0 ≤ c.num := (Rat.num_nonneg c).mpr (Rat.le_of_lt 0 c hc)
          refine Int.mul_le_mul_of_nonneg_left ?_ this
          rw [<- Int.mul_assoc,
              <- Int.mul_assoc,
              Int.mul_comm n₁ c.den,
              Int.mul_comm n₂ c.den,
              Int.mul_assoc,
              Int.mul_assoc]
          exact Int.mul_le_mul_of_nonneg_left h (Int.ofNat_zero_le c.den)

private theorem Rat.mul_le_mul_left' {c x y : Rat} (hc : c ≥ 0) : x ≤ y → (c * x ≤ c * y) := by
  intro h
  have : 0 = c ∨ 0 < c := (le_iff_eq_or_lt 0 c).mp hc
  cases this
  next heq =>
    rw [<- heq]
    simp
  next hlt =>
    exact (Rat.mul_le_mul_left hlt).mpr h

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
        have c_den_pos : (0 : Int) < c.den := Int.cast_pos' fun a => foo (congrArg Nat.cast a)
        have d1_pos : (0 : Int) < d₁ := Int.cast_pos' h₁
        have d2_pos : (0 : Int) < d₂ := Int.cast_pos' h₂
        have den_pos1 : (0 : Int) < c.den * d₁ := Int.mul_pos c_den_pos d1_pos
        have den_pos2 : (0 : Int) < c.den * d₂ := Int.mul_pos c_den_pos d2_pos
        rw [Rat.divInt_lt_divInt den_pos1 den_pos2]
        rw [Rat.divInt_lt_divInt d1_pos d2_pos]
        intro h
        have c_pos : 0 < c.num := (divInt_pos_iff_of_pos_right c_den_pos).mp h
        constructor
        · intro h2
          rw [Int.mul_assoc] at h2
          rw [Int.mul_assoc] at h2
          have h2' := Int.lt_of_mul_lt_mul_left (a := c.num) h2 (Int.le_of_lt c_pos)
          rw [<- Int.mul_assoc, <- Int.mul_assoc, Int.mul_comm n₁ c.den, Int.mul_comm n₂ c.den] at h2'
          rw [Int.mul_assoc, Int.mul_assoc] at h2'
          exact Int.lt_of_mul_lt_mul_left (a := c.den) h2' (Int.ofNat_zero_le c.den)
        · intro h2
          have h2' := Int.mul_lt_mul_of_pos_left h2 c_pos
          have h2'' := Int.mul_lt_mul_of_pos_left h2' c_den_pos
          rw [<- Int.mul_assoc] at h2''
          rw [<- Int.mul_assoc] at h2''
          rw [<- Int.mul_assoc] at h2''
          rw [<- Int.mul_assoc] at h2''
          rw [Int.mul_comm c.den c.num] at h2''
          rw [Int.mul_assoc c.num c.den n₁] at h2''
          rw [Int.mul_comm c.den n₁] at h2''
          rw [<- Int.mul_assoc] at h2''
          rw [Int.mul_assoc] at h2''
          rw [Int.mul_assoc c.num c.den n₂] at h2''
          rw [Int.mul_comm c.den n₂] at h2''
          rw [<- Int.mul_assoc c.num n₂ c.den] at h2''
          rw [Int.mul_assoc (c.num * n₂) c.den d₁] at h2''
          exact h2''

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

namespace Smt.Reconstruct.Rat

variable {a b c d x₁ x₂ y₁ y₂ : Rat}

theorem add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b :=
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

theorem le_trans (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
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

theorem lt_of_le_not_le (hab : a ≤ b) (hba : ¬ b ≤ a) : a < b := (Rat.lt_iff_le_not_le _ _).mpr ⟨hab, hba⟩

theorem le_of_lt (hab : a < b) : a ≤ b := ((Rat.lt_iff_le_not_le _ _).1 hab).1

theorem not_le_of_lt (hab : a < b) : ¬ b ≤ a := ((Rat.lt_iff_le_not_le _ _).1 hab).2

theorem lt_of_lt_of_le (hab : a < b) (hbc : b ≤ c) : a < c :=
  lt_of_le_not_le (le_trans (le_of_lt hab) hbc) fun hca ↦ not_le_of_lt hab (le_trans hbc hca)

theorem lt_trans (hab : a < b) (hbc : b < c) : a < c := lt_of_lt_of_le hab (le_of_lt hbc)

theorem lt_of_le_of_lt (hab : a ≤ b) (hbc : b < c) : a < c :=
  lt_of_le_not_le (le_trans hab (le_of_lt hbc)) fun hca ↦ not_le_of_lt hbc (le_trans hca hab)

theorem sum_ub₁ (h₁ : a < b) (h₂ : c < d) : a + c < b + d := by
  have h' : c + a < c + b := Rat.add_lt_add_left.mpr h₁
  have h'' : b + c < b + d := Rat.add_lt_add_left.mpr h₂
  rewrite [Rat.add_comm, Rat.add_comm c b] at h'
  exact lt_trans h' h''

theorem sum_ub₂ (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d := by
  have h' : c + a < c + b := Rat.add_lt_add_left.mpr h₁
  have h'' : b + c ≤ b + d := Rat.add_le_add_left.mpr h₂
  rewrite [Rat.add_comm, Rat.add_comm c b] at h'
  exact lt_of_lt_of_le h' h''

theorem sum_ub₃ (h₁ : a < b) (h₂ : c = d) : a + c < b + d := by
  rewrite [h₂]
  have : d + a < d + b := Rat.add_lt_add_left.mpr h₁
  rewrite [Rat.add_comm, Rat.add_comm d b] at this
  exact this

theorem sum_ub₄ (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d := by
  have h' : c + a ≤ c + b := Rat.add_le_add_left.mpr h₁
  have h'' : b + c < b + d := Rat.add_lt_add_left.mpr h₂
  rewrite [Rat.add_comm, Rat.add_comm c b] at h'
  exact lt_of_le_of_lt h' h''

theorem sum_ub₅ (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  have h' : c + a ≤ c + b := Rat.add_le_add_left.mpr h₁
  have h'' : b + c ≤ b + d := Rat.add_le_add_left.mpr h₂
  rewrite [Rat.add_comm, Rat.add_comm c b] at h'
  exact le_trans h' h''

theorem sum_ub₆ (h₁ : a ≤ b) (h₂ : c = d) : a + c ≤ b + d := by
  rewrite [h₂, Rat.add_comm, Rat.add_comm b d]
  exact Rat.add_le_add_left.mpr h₁

theorem sum_ub₇ (h₁ : a = b) (h₂ : c < d) : a + c < b + d := by
  rewrite [h₁, Rat.add_comm b c, Rat.add_comm b d]
  exact sum_ub₃ h₂ rfl

theorem sum_ub₈ (h₁ : a = b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  rewrite [h₁]
  exact Rat.add_le_add_left.mpr h₂

theorem sum_ub₉ (h₁ : a = b) (h₂ : c = d) : a + c = b + d := by
  rw [h₁, h₂]

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
  exact trichotomy₃ (Ne.symm h₁) h₂

theorem trichotomy₅ (h₁ : a ≥ b) (h₂ : a ≤ b) : a = b := by
  exact Rat.le_antisymm h₂ h₁

theorem trichotomy₆ (h₁ : a ≥ b) (h₂ : a ≠ b) : a > b := by
  exact trichotomy₃ (Ne.symm h₂) h₁

theorem abs_elim {x : Rat} : x.abs = if x < 0 then -x else x :=
  rfl

theorem abs_eq {a b : Rat} (hb : 0 ≤ b) : a.abs = b ↔ a = b ∨ a = -b := by
  unfold Rat.abs
  cases Classical.em (a < 0)
  next hl =>
    simp [hl]
    constructor
    · intro h
      right
      have := congrArg (fun x => -x) h
      simp at this
      exact this
    · intro h
      cases h
      next h1 =>
        rw [h1] at hl
        apply False.elim
        have := lt_of_le_of_lt hb hl
        exact (Bool.eq_not_self (Rat.blt 0 0)).mp this
      next h2 =>
        have := congrArg (fun x => -x) h2
        simp at this
        exact this
  next hr =>
    simp [hr]
    intro h
    have := Rat.not_lt.mp hr
    rw [h] at this
    have : 0 = b := Eq.symm (Rat.nonneg_antisymm b hb this)
    rw [<- this] at h
    simp at h
    exact trans h this

theorem neg_of_pos {a : Rat} : 0 < a → -a < 0 := by
  intro h
  rw [<- Rat.neg_self_add a]
  have : -a = -a + 0 := by simp
  conv =>
    lhs
    rw [this]
    skip
  exact sum_ub₇ rfl h

theorem pos_of_neg {a : Rat} : a < 0 → 0 < -a := by
  intro h
  rw [<- Rat.neg_self_add a]
  have : -a = -a + 0 := by simp
  conv =>
    rhs
    rw [this]
    skip
  exact sum_ub₇ rfl h

theorem abs_nonneg (x : Rat) : 0 ≤ x.abs := by
  unfold Rat.abs
  split
  next hx =>
    have := pos_of_neg hx
    exact le_of_lt this
  next hx =>
    exact Rat.not_lt.mp hx

theorem abs_of_nonpos (h : a ≤ 0) : a.abs = -a := by
  unfold Rat.abs
  split
  next => rfl
  next hx =>
    have := Rat.not_lt.mp hx
    have : a = 0 := trichotomy₅ this h
    rw [this]
    simp

theorem abs_of_nonneg {a : Rat} (h : 0 ≤ a) : a.abs = a := by
  unfold Rat.abs
  split
  next hx =>
    have : a ≤ 0 := le_of_lt hx
    have : a = 0 := trichotomy₅ h this
    rw [this]
    simp
  next => rfl

theorem abs_mul (a b : Rat) : (a * b).abs = a.abs * b.abs := by
  rw [Rat.abs_eq (Rat.mul_nonneg (Rat.abs_nonneg a) (Rat.abs_nonneg b))]
  rcases Rat.le_total a 0 with ha | ha <;> rcases Rat.le_total b 0 with hb | hb <;>
    simp only [Rat.abs_of_nonpos, Rat.abs_of_nonneg, true_or, or_true, Rat.neg_mul,
      Rat.mul_neg, Rat.neg_neg, *]

theorem mul_abs₁ (h₁ : x₁.abs = y₁.abs) (h₂ : x₂.abs = y₂.abs) : (x₁ * x₂).abs = (y₁ * y₂).abs := by
  rw [Rat.abs_mul x₁ x₂, Rat.abs_mul y₁ y₂, h₁, h₂]

theorem mul_abs₂ (h₁ : x₁.abs > y₁.abs) (h₂ : x₂.abs = y₂.abs ∧ x₂.abs ≠ 0) : (x₁ * x₂).abs > (y₁ * y₂).abs := by
  obtain ⟨hxy, hx⟩ := h₂
  rw [Rat.abs_mul, Rat.abs_mul]
  rw [<- hxy]
  rw [Rat.mul_comm, Rat.mul_comm (y₁.abs)]
  refine (Rat.mul_lt_mul_left ?_).mpr h₁
  · have : 0 ≤ x₂.abs := abs_nonneg x₂
    exact trichotomy₃ (Ne.symm hx) this

theorem mul_abs₃ (h₁ : x₁.abs > y₁.abs) (h₂ : x₂.abs > y₂.abs) : (x₁ * x₂).abs > (y₁ * y₂).abs := by
  rw [Rat.abs_mul, Rat.abs_mul]
  show y₁.abs * y₂.abs < x₁.abs * x₂.abs
  have : 0 < x₁.abs := lt_of_le_of_lt (abs_nonneg y₁) h₁
  have lt : x₁.abs * y₂.abs < x₁.abs * x₂.abs := (Rat.mul_lt_mul_left this).mpr h₂
  have le : y₁.abs * y₂.abs ≤ x₁.abs * y₂.abs := by
    rw [Rat.mul_comm, Rat.mul_comm x₁.abs]
    have : 0 ≤ y₂.abs := abs_nonneg y₂
    apply Rat.mul_le_mul_left' this
    exact le_of_lt h₁
  exact lt_of_le_of_lt le lt

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
      have foo' : (0 : Int) < da := Int.cast_pos' da_nz
      have bar' : (0 : Int) < db := Int.cast_pos' db_nz
      have : ((0 : Int) < da * db) := Int.mul_pos foo' bar'
      rw [Rat.divInt_pos_iff_of_pos_right this]
      have : ((0 : Int) < db * da) := Int.mul_pos bar' foo'
      rw [Rat.divInt_pos_iff_of_pos_right this] at h'
      simp only [Int.neg_mul, Int.sub_neg, gt_iff_lt]
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
      have foo' : (0 : Int) < da := Int.cast_pos' da_nz
      have bar' : (0 : Int) < db := Int.cast_pos' db_nz
      have : ((0 : Int) < da * db) := Int.mul_pos foo' bar'
      rw [Rat.divInt_nonneg_iff_of_pos_right this]
      have : ((0 : Int) < db * da) := Int.mul_pos bar' foo'
      rw [Rat.divInt_nonneg_iff_of_pos_right this] at h'
      simp only [Int.neg_mul, Int.sub_neg, ge_iff_le]
      rw [Int.add_comm, <- Int.sub_eq_add_neg]
      exact h'

theorem int_tight_lb {i : Int} (h : i > c) : i ≥ c.floor + 1 := by
  cases Int.lt_trichotomy i (c.floor + 1) with
  | inl iltc =>
    have ilec := (Int.lt_iff_add_one_le).mp iltc
    have h2 : i ≤ c.floor := by exact (Int.add_le_add_iff_right 1).mp iltc
    have c_le_floor := Rat.floor_le_self c
    have : i ≤ c := Rat.le_trans (Rat.cast_le.mp h2) c_le_floor
    have abs := Rat.lt_of_le_of_lt this h
    apply False.elim
    exact Rat.lt_irrefl _ abs
  | inr h' =>
    cases h' with
    | inl ieqc => exact Int.le_of_eq (id (Eq.symm ieqc))
    | inr igtc => exact Int.le_of_lt igtc

theorem floor_neg : Rat.floor (-a) = -Rat.ceil' a := by
  simp [Rat.ceil']

theorem int_tight_ub {i : Int} (h : i < c) : i ≤ c.ceil' - 1 := by
  have h' := Rat.neg_lt_neg h
  have i_le_floor_neg_c := int_tight_lb h'
  rw [floor_neg] at i_le_floor_neg_c
  have pf := Int.neg_le_neg i_le_floor_neg_c
  simp [Int.add_comm, Int.neg_add] at pf
  rw [Int.add_comm] at pf
  rw [Int.sub_eq_add_neg]
  exact pf

theorem lt_eq_sub_lt_zero : (a < b) = (a - b < 0) := by
  apply propext
  rw [Rat.lt_iff_sub_pos]
  constructor
  · intro h
    have h' := Rat.neg_lt_neg h
    rw [Rat.neg_sub] at h'
    exact h'
  · intro h
    have h' := Rat.neg_lt_neg h
    simp at h'
    rw [Rat.neg_sub] at h'
    exact h'

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
  · intro h
    have h' := congrArg (fun z => z + b) h
    simp [Rat.zero_add, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_self_add, Rat.add_zero] at h'
    exact h'

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

theorem mul_sign₁ : a < 0 → b < 0 → a * b > 0 :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz ha =>
    Rat.numDenCasesOn' b fun b_num b_den b_den_nz hb => by
      have : 0 < a_den := Nat.zero_lt_of_ne_zero a_den_nz
      have a_den_pos : (0 : Int) < a_den := Int.natCast_pos.mpr this
      have a_num_neg : a_num < 0 := (Rat.divInt_neg_iff_of_neg_right a_den_pos).mp ha
      have : 0 < b_den := Nat.zero_lt_of_ne_zero b_den_nz
      have b_den_pos : (0 : Int) < b_den := Int.natCast_pos.mpr this
      have b_num_neg : b_num < 0 := (Rat.divInt_neg_iff_of_neg_right b_den_pos).mp hb
      have bar : (a_den : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr a_den_nz
      have bar' : (b_den : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr b_den_nz
      rw [Rat.divInt_mul_divInt _ _ bar bar']
      have : 0 < (a_den : Int) * b_den := Int.mul_pos a_den_pos b_den_pos
      apply (Rat.divInt_pos_iff_of_pos_right this).mpr
      exact Int.mul_pos_of_neg_of_neg a_num_neg b_num_neg

theorem mul_sign₃ : a < 0 → b > 0 → a * b < 0 :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz ha =>
    Rat.numDenCasesOn' b fun b_num b_den b_den_nz hb => by
      have : 0 < a_den := Nat.zero_lt_of_ne_zero a_den_nz
      have a_den_pos : (0 : Int) < a_den := Int.natCast_pos.mpr this
      have a_num_neg : a_num < 0 := (Rat.divInt_neg_iff_of_neg_right a_den_pos).mp ha
      have : 0 < b_den := Nat.zero_lt_of_ne_zero b_den_nz
      have b_den_pos : (0 : Int) < b_den := Int.natCast_pos.mpr this
      have b_num_neg : 0 < b_num := (Rat.divInt_pos_iff_of_pos_right b_den_pos).mp hb
      have bar : (a_den : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr a_den_nz
      have bar' : (b_den : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr b_den_nz
      rw [Rat.divInt_mul_divInt _ _ bar bar']
      have : 0 < (a_den : Int) * b_den := Int.mul_pos a_den_pos b_den_pos
      apply (Rat.divInt_neg_iff_of_neg_right this).mpr
      exact Int.mul_neg_of_neg_of_pos a_num_neg b_num_neg

theorem mul_sign₄ (ha : a > 0) (hb : b < 0) : a * b < 0 := by
  rw [Rat.mul_comm]
  exact mul_sign₃ hb ha

theorem le_mul_of_lt_of_le (a b : Rat) : a < 0 → b ≤ 0 → 0 ≤ a * b := by
  intros h1 h2
  cases (Rat.le_iff_eq_or_lt b 0).mp h2 with
  | inl heq => rw [heq, Rat.mul_zero]; exact rfl
  | inr hlt => have := mul_sign₁ h1 hlt; exact le_of_lt this

theorem nonpos_of_mul_nonneg (a b : Rat) : a < 0 → 0 ≤ a * b → b ≤ 0 := by
  intros h1 h2
  apply Classical.byContradiction
  intro h3
  have : 0 < b := (Rat.not_nonpos _).mp h3
  have : a * b < 0 := mul_sign₃ h1 this
  have := Rat.lt_of_lt_of_le this h2
  exact Rat.lt_irrefl _ this

theorem neg_of_mul_pos (a b : Rat) : a < 0 → 0 < a * b → b < 0 := by
  intros h1 h2
  apply Classical.byContradiction
  intro h3
  have : 0 ≤ b := Rat.not_lt.mp h3
  cases (Rat.le_iff_eq_or_lt 0 b).mp this with
  | inl heq => rw [<-heq, Rat.mul_zero] at h2; exact Rat.lt_irrefl _ h2
  | inr hlt => have := mul_sign₃ h1 hlt; have := Rat.lt_trans h2 this; exact Rat.lt_irrefl _ this

theorem le_iff_sub_nonneg' (x y : Rat) : y ≤ x ↔ y - x ≤ 0 := by
  rw [Rat.le_iff_sub_nonneg]
  rw [Rat.nonneg_iff_sub_nonpos]
  rw [Rat.neg_sub]

theorem lt_iff_sub_pos' (x y : Rat) : y < x ↔ y - x < 0 := by
  rw [Rat.lt_iff_sub_pos]
  rw [Rat.pos_iff_neg_nonpos]
  rw [Rat.neg_sub]

theorem lt_of_sub_eq_neg' {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) → (b₁ < b₂) := by
  intro h2
  have := (Rat.lt_iff_sub_pos' a₂ a₁).mp h2
  have : 0 < c₁ * (a₁ - a₂) := mul_sign₁ hc₁ this
  rw [h] at this
  have := neg_of_mul_pos c₂ (b₁ - b₂) hc₂ this
  exact (lt_iff_sub_pos' b₂ b₁).mpr this

theorem lt_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  apply propext
  constructor
  · exact lt_of_sub_eq_neg' hc₁ hc₂ h
  · intro h2
    exact lt_of_sub_eq_neg' (c₁ := c₂) (c₂ := c₁) (a₁ := b₁) (a₂ := b₂) (b₁ := a₁) (b₂ := a₂) hc₂ hc₁ (Eq.symm h) h2

theorem le_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) ≤ 0) = (x - y ≤ 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, Rat.mul_le_mul_left hc]
  rw [le_eq_sub_le_zero, @le_eq_sub_le_zero b₁, ← this hc₁, ← this hc₂, h]

theorem le_of_sub_eq_neg' {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) → (b₁ ≤ b₂) := by
  intro h2
  have := (Rat.le_iff_sub_nonneg' a₂ a₁).mp h2
  have : 0 ≤ c₁ * (a₁ - a₂) := le_mul_of_lt_of_le c₁ (a₁ - a₂) hc₁ this
  rw [h] at this
  have := nonpos_of_mul_nonneg c₂ (b₁ - b₂) hc₂ this
  exact (Rat.le_iff_sub_nonneg' b₂ b₁).mpr this

theorem le_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  apply propext
  constructor
  · exact le_of_sub_eq_neg' hc₁ hc₂ h
  · intro h2
    exact le_of_sub_eq_neg' (c₁ := c₂) (c₂ := c₁) (a₁ := b₁) (a₂ := b₂) (b₁ := a₁) (b₂ := a₂) hc₂ hc₁ (Eq.symm h) h2

theorem eq_of_sub_eq {c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  apply propext
  apply Iff.intro
  · intro ha
    rw [ha] at h
    simp at h
    have := Rat.mul_eq_zero_left hc₂ (Eq.symm h)
    rw [eq_eq_sub_eq_zero]
    exact this
  · intro hb
    rw [hb] at h
    simp at h
    have := Rat.mul_eq_zero_left hc₁ h
    rw [eq_eq_sub_eq_zero]
    exact this

theorem ge_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) ≥ 0) = (x - y ≥ 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, ge_iff_le, Rat.mul_le_mul_left hc]
  rw [ge_eq_sub_ge_zero, @ge_eq_sub_ge_zero b₁, ← this hc₁, ← this hc₂, h]

theorem mul_neg (a b : Rat) : a * (-b) = - (a * b) :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz =>
    Rat.numDenCasesOn' b fun b_num b_den b_den_nz => by
      rw [Rat.divInt_mul_divInt _ _ (Int.ofNat_ne_zero.mpr a_den_nz) (Int.ofNat_ne_zero.mpr b_den_nz)]
      rw [Rat.neg_divInt]
      rw [Rat.divInt_mul_divInt _ _ (Int.ofNat_ne_zero.mpr a_den_nz) (Int.ofNat_ne_zero.mpr b_den_nz)]
      rw [Int.mul_neg, Rat.neg_divInt]

theorem neg_eq {a b : Rat} : -a = -b → a = b := by
  intro h
  have h' := congrArg (fun z => -z) h
  simp only [Rat.neg_neg] at h'
  exact h'

theorem ge_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  show (a₂ ≤ a₁) = (b₂ ≤ b₁)
  rw [<- Rat.neg_sub, <- Rat.neg_sub (x := b₂) (y := b₁), mul_neg, mul_neg] at h
  have h' := neg_eq h
  exact le_of_sub_eq_neg hc₁ hc₂ h'

theorem gt_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) > 0) = (x - y > 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, gt_iff_lt, Rat.mul_lt_mul_left hc]
  rw [gt_eq_sub_gt_zero, @gt_eq_sub_gt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem gt_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  show (a₂ < a₁) = (b₂ < b₁)
  rw [<- Rat.neg_sub, <- Rat.neg_sub (x := b₂) (y := b₁), mul_neg, mul_neg] at h
  have h' := neg_eq h
  exact lt_of_sub_eq_neg hc₁ hc₂ h'

theorem lt_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_lt]
  exact lt_of_sub_eq_pos hc₁ hc₂ h

theorem lt_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_lt]
  exact lt_of_sub_eq_neg hc₁ hc₂ h

theorem le_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_le]
  exact le_of_sub_eq_pos hc₁ hc₂ h

theorem le_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_le]
  exact le_of_sub_eq_neg hc₁ hc₂ h

theorem eq_of_sub_eq_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_eq]
  exact eq_of_sub_eq hc₁ hc₂ h

theorem ge_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_ge]
  exact ge_of_sub_eq_pos hc₁ hc₂ h

theorem ge_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_ge]
  exact ge_of_sub_eq_neg hc₁ hc₂ h

theorem gt_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_gt]
  exact gt_of_sub_eq_pos hc₁ hc₂ h

theorem gt_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_gt]
  exact gt_of_sub_eq_neg hc₁ hc₂ h

theorem lt_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_lt]
  exact lt_of_sub_eq_pos hc₁ hc₂ h

theorem lt_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_lt]
  exact lt_of_sub_eq_neg hc₁ hc₂ h

theorem le_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_le]
  exact le_of_sub_eq_pos hc₁ hc₂ h

theorem le_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_le]
  exact le_of_sub_eq_neg hc₁ hc₂ h

theorem eq_of_sub_eq_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_eq]
  exact eq_of_sub_eq hc₁ hc₂ h

theorem ge_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_ge]
  exact ge_of_sub_eq_pos hc₁ hc₂ h

theorem ge_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_ge]
  exact ge_of_sub_eq_neg hc₁ hc₂ h

theorem gt_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_gt]
  exact gt_of_sub_eq_pos hc₁ hc₂ h

theorem gt_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_gt]
  exact gt_of_sub_eq_neg hc₁ hc₂ h

theorem mul_sign₆ : a > 0 → b > 0 → a * b > 0 :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz ha =>
    Rat.numDenCasesOn' b fun b_num b_den b_den_nz hb => by
      have : 0 < a_den := Nat.zero_lt_of_ne_zero a_den_nz
      have a_den_pos : (0 : Int) < a_den := Int.natCast_pos.mpr this
      have a_num_pos : 0 < a_num := (Rat.divInt_pos_iff_of_pos_right a_den_pos).mp ha
      have : 0 < b_den := Nat.zero_lt_of_ne_zero b_den_nz
      have b_den_pos : (0 : Int) < b_den := Int.natCast_pos.mpr this
      have b_num_pos : 0 < b_num := (Rat.divInt_pos_iff_of_pos_right b_den_pos).mp hb
      have bar : (a_den : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr a_den_nz
      have bar' : (b_den : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr b_den_nz
      rw [Rat.divInt_mul_divInt _ _ bar bar']
      have : 0 < (a_den : Int) * b_den := Int.mul_pos a_den_pos b_den_pos
      apply (Rat.divInt_pos_iff_of_pos_right this).mpr
      exact Int.mul_pos a_num_pos b_num_pos

theorem Int.square_pos {i : Int} : i ≠ 0 → 0 < i * i := by
  intro h
  cases Int.lt_or_lt_of_ne h with
  | inl h' => exact Int.mul_pos_of_neg_of_neg h' h'
  | inr h' => exact Int.mul_pos h' h'

theorem mul_sign₀ : a ≠ 0 → a * a > 0 :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz ha => by
    have : a_num ≠ 0 := (Rat.mkRat_ne_zero a_den_nz).mp ha
    have : 0 < a_num * a_num := Int.square_pos this
    have bar : (a_den : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr a_den_nz
    have foo : (0 : Int) < a_den * a_den := Int.square_pos bar
    rw [Rat.divInt_mul_divInt _ _ bar bar]
    exact (Rat.divInt_pos_iff_of_pos_right foo).mpr this

theorem mul_sign₂ (ha : a < 0) (hb : b ≠ 0) : a * b * b < 0 := by
  have := mul_sign₀ hb
  rw [Rat.mul_assoc]
  exact mul_sign₃ ha this

theorem mul_sign₅ (ha : a > 0) (hb : b ≠ 0) : a * b * b > 0 := by
  have := mul_sign₀ hb
  rw [Rat.mul_assoc]
  exact mul_sign₆ ha this

theorem mul_pos_lt (h : c > 0 ∧ a < b) : c * a < c * b := by
  have ⟨h1, h2⟩ := h
  exact (Rat.mul_lt_mul_left h1).mpr h2

theorem mul_pos_le (h : c > 0 ∧ a ≤ b) : c * a ≤ c * b := by
  have ⟨h1, h2⟩ := h
  exact (Rat.mul_le_mul_left h1).mpr h2

theorem mul_pos_gt (h : c > 0 ∧ a > b) : c * a > c * b := mul_pos_lt h

theorem mul_pos_ge (h : c > 0 ∧ a ≥ b) : c * a ≥ c * b := mul_pos_le h

theorem mul_pos_eq (h : c > 0 ∧ a = b) : c * a = c * b := by rw [h.2]

theorem mul_neg_lt : (c < 0 ∧ a < b) → c * a > c * b :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz =>
    Rat.numDenCasesOn' b fun b_num b_den b_den_nz =>
      Rat.numDenCasesOn' c fun c_num c_den c_den_nz => by
        rintro ⟨h1, h2⟩
        rw [Rat.divInt_mul_divInt _ _ (Int.ofNat_ne_zero.mpr c_den_nz) (Int.ofNat_ne_zero.mpr a_den_nz)]
        rw [Rat.divInt_mul_divInt _ _ (Int.ofNat_ne_zero.mpr c_den_nz) (Int.ofNat_ne_zero.mpr b_den_nz)]
        have c_den_pos : (0 : Int) < c_den := Int.cast_pos' c_den_nz
        have a_den_pos : (0 : Int) < a_den := Int.cast_pos' a_den_nz
        have b_den_pos : (0 : Int) < b_den := Int.cast_pos' b_den_nz
        have : c_num < 0 := (Rat.divInt_neg_iff_of_neg_right c_den_pos).mp h1
        have h3 := (Rat.divInt_lt_divInt a_den_pos b_den_pos).mp h2
        have ca_pos : (0 : Int) < c_den * a_den := Int.mul_pos c_den_pos a_den_pos
        have cb_pos : (0 : Int) < c_den * b_den := Int.mul_pos c_den_pos b_den_pos
        show (Rat.divInt (c_num * b_num) (↑c_den * ↑b_den) < Rat.divInt (c_num * a_num) (↑c_den * ↑a_den))
        rw [(Rat.divInt_lt_divInt cb_pos ca_pos)]
        have c_num_neg : c_num < 0 := (Rat.divInt_neg_iff_of_neg_right c_den_pos).mp h1
        rw [Int.mul_assoc, Int.mul_assoc]
        apply Int.mul_lt_mul_of_neg_left _ c_num_neg
        rw [Int.mul_comm, Int.mul_comm b_num (c_den * a_den)]
        rw [Int.mul_assoc, Int.mul_assoc]
        apply Int.mul_lt_mul_of_pos_left _ c_den_pos
        rw [Int.mul_comm, Int.mul_comm a_den b_num]
        exact h3

theorem mul_neg_gt (h : c < 0 ∧ a > b) : c * a < c * b := mul_neg_lt h

theorem mul_neg_eq (h : c < 0 ∧ a = b) : c * a = c * b := by rw [h.2]

theorem Int.mul_le_mul_of_neg_left {a b c : Int} (h : b ≤ a) (hc : c < 0) : c * a ≤ c * b :=
  match Int.le_iff_eq_or_lt.mp h with
  | Or.inl heq => by rw [heq]; exact Int.le_refl (c * a)
  | Or.inr hlt => by have := Int.mul_lt_mul_of_neg_left hlt hc; exact Int.le_of_lt this

theorem Int.mul_le_mul_of_pos_left {a b c : Int} (h : a ≤ b) (hc : 0 < c) : c * a ≤ c * b :=
  match Int.le_iff_eq_or_lt.mp h with
  | Or.inl heq => by rw [heq]; exact Int.le_refl (c * b)
  | Or.inr hlt => by have := Int.mul_lt_mul_of_pos_left hlt hc; exact Int.le_of_lt this

theorem Rat.neg_mul (a b : Rat) : -a * b = - (a * b) := by
  rw [Rat.mul_comm]
  rw [Rat.mul_neg]
  rw [Rat.mul_comm]

theorem Int.ge_of_mul_le_mul_left_neg {a b c : Int} (w : a * b ≤ a * c) (h : a < 0) : c ≤ b := by
  have w := Int.sub_nonneg_of_le w
  rw [← Int.mul_sub] at w
  have w := Int.ediv_nonpos_of_nonneg_of_nonpos w (Int.le_of_lt h)
  rw [Int.mul_ediv_cancel_left _ (Int.ne_of_lt h)] at w
  exact Int.le_of_sub_nonpos w

theorem Int.mul_le_mul_neg {a b c : Int} (h : a < 0) : a * b ≤ a * c <-> c ≤ b :=
  ⟨fun x => ge_of_mul_le_mul_left_neg x h , fun x => mul_le_mul_of_neg_left x h⟩

theorem Rat.mul_le_mul_of_neg_left (a b c : Rat) : c < 0 -> (a ≤ b <-> c * a ≥ c * b) :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz =>
    Rat.numDenCasesOn' b fun b_num b_den b_den_nz =>
      Rat.numDenCasesOn' c fun c_num c_den c_den_nz => by
        intro h1
        have : (0 : Int) < c_den := Int.cast_pos' c_den_nz
        have c_num_neg : c_num < 0 := (Rat.divInt_neg_iff_of_neg_right this).mp h1
        clear h1
        have a_den_pos : (0 : Int) < a_den := Int.cast_pos' a_den_nz
        have b_den_pos : (0 : Int) < b_den := Int.cast_pos' b_den_nz
        have c_den_pos : (0 : Int) < c_den := Int.cast_pos' c_den_nz
        have a_den_nz' : (a_den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr a_den_nz
        have b_den_nz' : (b_den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr b_den_nz
        have c_den_nz' : (c_den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr c_den_nz
        have ca_den_pos : (0 : Int) < c_den * a_den := Int.mul_pos this a_den_pos
        have cb_den_pos : (0 : Int) < c_den * b_den := Int.mul_pos this b_den_pos
        rw [Rat.divInt_le_divInt a_den_pos b_den_pos]
        rw [Rat.divInt_mul_divInt _ _ c_den_nz' a_den_nz']
        rw [Rat.divInt_mul_divInt _ _ c_den_nz' b_den_nz']
        show a_num * ↑b_den ≤ b_num * ↑a_den ↔ Rat.divInt _ _ ≤ Rat.divInt _ _
        rw [Rat.divInt_le_divInt cb_den_pos ca_den_pos]
        rw [Int.mul_assoc, Int.mul_assoc]
        rw [Int.mul_le_mul_neg c_num_neg]
        rw [Int.mul_comm a_num (c_den * b_den)]
        rw [Int.mul_comm b_num (c_den * a_den)]
        rw [Int.mul_assoc, Int.mul_assoc]
        constructor
        · intro h2; rw [Int.mul_comm b_den a_num, Int.mul_comm a_den b_num]; exact Int.mul_le_mul_of_pos_left h2 this
        · intro h2; rw [Int.mul_comm a_num b_den, Int.mul_comm b_num a_den]; exact Int.le_of_mul_le_mul_left h2 this

theorem mul_neg_le (h : c < 0 ∧ a ≤ b) : c * a ≥ c * b := (Rat.mul_le_mul_of_neg_left a b c h.1).mp h.2

theorem mul_neg_ge (h : c < 0 ∧ a ≥ b) : c * a ≤ c * b :=
  mul_neg_le h

theorem mul_tangent_mp_lower (h : x * y ≤ b * x + a * y - a * b)
  : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b := by
  apply Classical.or_iff_not_imp_right.mpr
  have h := Rat.add_le_add_left (c := (- b * x)).mpr h
  rw [Rat.sub_eq_add_neg] at h
  rw [Rat.add_assoc (b * x)] at h
  rw [<- Rat.add_assoc (-b * x) (b * x) (a * y + -(a * b))] at h
  rw [Rat.neg_mul] at h
  rw [Rat.neg_self_add] at h
  rw [Rat.zero_add] at h
  rw [<- Rat.neg_mul, Rat.mul_comm] at h
  rw [<- Rat.mul_add x (-b) y] at h
  rw [<- Rat.mul_neg] at h
  rw [<- Rat.mul_add] at h
  rw [Rat.add_comm] at h
  rw [<- Rat.sub_eq_add_neg] at h
  intro h2
  have h2 := Classical.not_and_iff_not_or_not.mp h2
  rw [Rat.not_le, Rat.not_le] at h2
  cases h2 with
  | inl h2 =>
    constructor
    · exact le_of_lt h2
    · apply Classical.byContradiction
      intro h3
      rw [Rat.not_le] at h3
      have h3 := (Rat.lt_iff_sub_pos' _ _).mp h3
      rw [Rat.mul_comm, Rat.mul_comm a _] at h
      have := (Rat.mul_le_mul_of_neg_left _ _ _ h3).mpr h
      have := Rat.lt_of_lt_of_le h2 this
      exact Rat.lt_irrefl _ this
  | inr h2 =>
    rw [and_comm]
    constructor
    · exact le_of_lt h2
    · apply Classical.byContradiction
      intro h3
      rw [Rat.not_le] at h3
      rw [Rat.mul_comm, Rat.mul_comm a _] at h
      have : 0 < y - b := (Rat.lt_iff_sub_pos b y).mp h2
      rw [Rat.mul_le_mul_left this] at h
      exact Rat.lt_irrefl _ (Rat.lt_of_le_of_lt h h3)

theorem mul_tangent_mpr_lower (h : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b)
  : x * y ≤ b * x + a * y - a * b := by
  rw [<- Rat.add_le_add_left (c := -b * x)]
  rw [Rat.sub_eq_add_neg]
  rw [Rat.add_assoc (b * x)]
  rw [<- Rat.add_assoc (-b * x) (b * x) (a * y + -(a * b))]
  rw [Rat.neg_mul]
  rw [Rat.neg_self_add]
  rw [Rat.zero_add]
  rw [<- Rat.neg_mul, Rat.mul_comm]
  rw [<- Rat.mul_add x (-b) y]
  rw [<- Rat.mul_neg]
  rw [<- Rat.mul_add]
  rw [Rat.add_comm]
  rw [<- Rat.sub_eq_add_neg]
  rw [Rat.mul_comm, Rat.mul_comm a _]
  cases h with
  | inl h =>
    have ⟨h1, h2⟩ := h
    have : 0 ≤ y - b := (Rat.le_iff_sub_nonneg b y).mp h2
    cases (Rat.le_iff_eq_or_lt _ _).mp this with
    | inl eq => rw [<- eq]; simp only [Rat.zero_mul, ge_iff_le]; rfl
    | inr lt => rw [Rat.mul_le_mul_left lt]; exact h1
  | inr h =>
    have ⟨h1, h2⟩ := h
    have : y - b ≤ 0 := (le_iff_sub_nonneg' b y).mp h2
    cases (Rat.le_iff_eq_or_lt _ _).mp this with
    | inl eq => rw [eq]; simp only [Rat.zero_mul, ge_iff_le]; rfl
    | inr lt => show (y - b) * a ≥ (y - b) * x; rw [<- Rat.mul_le_mul_of_neg_left a x _ lt]; exact h1

theorem mul_tangent_lower :
  x * y ≤ b * x + a * y - a * b ↔ x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b :=
  ⟨mul_tangent_mp_lower, mul_tangent_mpr_lower⟩

theorem mul_tangent_lower_eq
  : (x * y ≤ b * x + a * y - a * b) = (x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b) :=
  propext (mul_tangent_lower)

theorem mul_tangent_mp_upper (h : x * y ≥ b * x + a * y - a * b)
  : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b := by
  apply Classical.or_iff_not_imp_right.mpr
  have h := Rat.add_le_add_left (c := (- b * x)).mpr h
  rw [Rat.sub_eq_add_neg (b * x + a * y) _] at h
  rw [Rat.add_assoc (b * x)] at h
  rw [<- Rat.add_assoc (-b * x) (b * x) (a * y + -(a * b))] at h
  rw [Rat.neg_mul] at h
  rw [Rat.neg_self_add] at h
  rw [Rat.zero_add] at h
  rw [<- Rat.neg_mul b, Rat.mul_comm (-b) x] at h
  rw [<- Rat.mul_add x (-b) y] at h
  rw [<- Rat.mul_neg] at h
  rw [<- Rat.mul_add] at h
  rw [Rat.add_comm (-b) y] at h
  rw [<- Rat.sub_eq_add_neg] at h
  rw [Rat.mul_comm, Rat.mul_comm x _] at h
  intro h2
  have h2 := Classical.not_and_iff_not_or_not.mp h2
  rw [Rat.not_le, Rat.not_le] at h2
  cases h2 with
  | inl h2 =>
    constructor
    · exact le_of_lt h2
    · apply Classical.byContradiction
      intro h3
      rw [Rat.not_le] at h3
      have : 0 < y - b := (Rat.lt_iff_sub_pos b y).mp h3
      rw [Rat.mul_le_mul_left this] at h
      exact Rat.lt_irrefl _ (Rat.lt_of_lt_of_le h2 h)
  | inr h2 =>
    constructor
    · have : y - b < 0 := by exact (lt_iff_sub_pos' b y).mp h2
      exact (Rat.mul_le_mul_of_neg_left _ _ _ this).mpr h
    · exact le_of_lt h2

theorem mul_tangent_mpr_upper (h : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b)
  : x * y ≥ b * x + a * y - a * b := by
  show _ ≤ _
  rw [<- Rat.add_le_add_left (c := -b * x)]
  show _ ≥ _
  rw [Rat.sub_eq_add_neg (b * x + a * y) _]
  rw [Rat.add_assoc (b * x)]
  rw [<- Rat.add_assoc (-b * x) (b * x) (a * y + -(a * b))]
  rw [Rat.neg_mul]
  rw [Rat.neg_self_add]
  rw [Rat.zero_add]
  rw [<- Rat.neg_mul, Rat.mul_comm]
  rw [<- Rat.mul_add x (-b) y]
  rw [<- Rat.mul_neg]
  rw [<- Rat.mul_add]
  rw [Rat.add_comm]
  rw [<- Rat.sub_eq_add_neg]
  rw [Rat.mul_comm, Rat.mul_comm a _]
  cases h with
  | inl h =>
    have ⟨h1, h2⟩ := h
    cases (Rat.le_iff_eq_or_lt y b).mp h2 with
    | inl eq => rw [eq]; simp only [Rat.sub_self, Rat.zero_mul, ge_iff_le]; rfl
    | inr lt =>
      have : y - b < 0 := (lt_iff_sub_pos' b y).mp lt
      exact (Rat.mul_le_mul_of_neg_left x a (y - b) this).mp h1
  | inr h =>
    have ⟨h1, h2⟩ := h
    cases (Rat.le_iff_eq_or_lt b y).mp h2 with
    | inl eq => rw [eq]; simp only [Rat.sub_self, Rat.zero_mul, ge_iff_le]; rfl
    | inr lt =>
      have : 0 < y - b := (Rat.lt_iff_sub_pos b y).mp lt
      show _ ≤ _
      rw [Rat.mul_le_mul_left this]
      exact h1

theorem mul_tangent_upper
  : x * y ≥ b * x + a * y - a * b ↔ x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b :=
  ⟨mul_tangent_mp_upper, mul_tangent_mpr_upper⟩

theorem mul_tangent_upper_eq
  : (x * y ≥ b * x + a * y - a * b) = (x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b) :=
  propext (mul_tangent_upper)

end Smt.Reconstruct.Rat
