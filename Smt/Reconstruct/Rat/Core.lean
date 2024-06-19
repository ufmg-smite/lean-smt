/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Batteries.Data.Rat


namespace Int
@[simp]
protected theorem natCast_eq_zero {n : Nat} : (n : Int) = 0 ↔ n = 0 := by
  omega

protected theorem natCast_ne_zero {n : Nat} : (n : Int) ≠ 0 ↔ n ≠ 0 := by
  exact not_congr Int.natCast_eq_zero

protected theorem gcd_def (i j : Int) : i.gcd j = i.natAbs.gcd j.natAbs :=
  rfl

protected theorem gcd_def' (i : Int) (j : Nat) : i.gcd (ofNat j) = i.natAbs.gcd j :=
  Int.gcd_def _ _

theorem gcd_eq_zero_iff {i j : Int} : gcd i j = 0 ↔ i = 0 ∧ j = 0 := by
  rw [gcd, Nat.gcd_eq_zero_iff, natAbs_eq_zero, natAbs_eq_zero]

theorem gcd_ne_zero_iff {i j : Int} : gcd i j ≠ 0 ↔ i ≠ 0 ∨ j ≠ 0 := by
  constructor
  · intro h
    let tmp := not_congr gcd_eq_zero_iff |>.mp h
    if h_i : i = 0 then
      simp [h_i] at tmp
      exact Or.inr tmp
    else
      exact Or.inl h_i
  · intro h gcd_zero
    rw [gcd_eq_zero_iff] at gcd_zero
    simp [gcd_zero.1, gcd_zero.2] at h

protected theorem dvd_mul_left_of_dvd {i j : Int} (k : Int) : i ∣ j → i ∣ k * j
| ⟨n, h⟩ => by
  rw [h]
  exists k * n
  rw [
    ← Int.mul_assoc k i n,
    Int.mul_comm k i,
    Int.mul_assoc i k n,
  ]

protected theorem dvd_mul_right_of_dvd {i j : Int} (k : Int) : i ∣ j → i ∣ j * k :=
  Int.mul_comm j k ▸ Int.dvd_mul_left_of_dvd k

theorem flatten_div_mul_eq_mul_div
  {i1 i2 i3 i4 j : Int}
  (j_pos : j ≠ 0)
  (j_dvd_i1 : j ∣ i1)
  (j_dvd_i4 : j ∣ i4)
: i1 / j * i2 = i3 * (i4 / j) → i1 * i2 = i3 * i4 := by
  intro h
  rw [← Int.mul_eq_mul_left_iff j_pos] at h
  conv at h =>
    lhs
    rw [← Int.mul_assoc]
    rw [← Int.mul_ediv_assoc _ j_dvd_i1]
    rw [Int.mul_ediv_cancel_left _ j_pos]
  conv at h =>
    rhs
    rw [← Int.mul_assoc]
    conv => lhs ; rw [Int.mul_comm]
    rw [Int.mul_assoc]
    rw [← Int.mul_ediv_assoc _ j_dvd_i4]
    rw [Int.mul_ediv_cancel_left _ j_pos]
  assumption
end Int



namespace Rat

theorem num_divInt_den (q : Rat) : q.num /. q.den = q :=
  divInt_self _

theorem mk'_eq_divInt {n d h c} : (⟨n, d, h, c⟩ : Rat) = n /. d :=
  (num_divInt_den _).symm

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



protected theorem add_comm (a b : Rat) : a + b = b + a := by
  simp [add_def, Int.add_comm, Int.mul_comm, Nat.mul_comm]

protected theorem add_zero : ∀ a : Rat, a + 0 = a
| ⟨num, den, _h, _h'⟩ => by
  simp [Rat.add_def]
  simp only [Rat.normalize_eq_mkRat, Rat.mk_eq_normalize]

protected theorem zero_add : ∀ a : Rat, 0 + a = a :=
  fun a => Rat.add_comm a 0 ▸ Rat.add_zero a

protected theorem eq_mkRat : ∀ a : Rat, a = mkRat a.num a.den := fun a => by
  simp [Rat.mkRat_def, a.den_nz, Rat.normalize_eq, a.reduced]

protected theorem mul_eq_zero_iff : ∀ {a b : Rat}, a * b = 0 ↔ a = 0 ∨ b = 0 := by
  intro a b
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

protected theorem mul_ne_zero_iff : ∀ {a b : Rat}, a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  intro a b
  simp only [not_congr (@Rat.mul_eq_zero_iff a b), not_or, ne_eq]

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



protected theorem add_assoc (a b c : Rat) : a + b + c = a + (b + c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ ↦
    numDenCasesOn' b fun n₂ d₂ h₂ ↦
      numDenCasesOn' c fun n₃ d₃ h₃ ↦ by
        simp only [
          ne_eq, Int.natCast_eq_zero, h₁, not_false_eq_true, h₂,
          divInt_add_divInt, Int.mul_eq_zero, or_self, h₃
        ]
        rw [Int.mul_assoc, Int.add_mul, Int.add_mul, Int.mul_assoc, Int.add_assoc]
        congr 2
        ac_rfl

protected theorem mul_assoc (a b c : Rat) : a + b + c = a + (b + c) :=
  numDenCasesOn' a fun n₁ d₁ _h₁ =>
    numDenCasesOn' b fun n₂ d₂ _h₂ =>
      numDenCasesOn' c fun n₃ d₃ _h₃ => by
        simp only [Rat.divInt_ofNat]
        exact Rat.add_assoc _ _ _
end Rat
