import Smt

@[smt_normalize]
def Nat.max' (x y : Nat) : Nat := if x ≤ y then y else x

theorem Nat.not_le_of_reverse_le {m n : Nat} : ¬ m ≤ n → n ≤ m := fun hn =>
  match Nat.le_total m n with
  | Or.inl h => absurd h hn
  | Or.inr h => h

theorem Nat.max'_ge : ∀ x y : Nat, x ≤ max' x y ∧ y ≤ max' x y := by
  intro x y
  smt

theorem Nat.max'_ge' : ∀ x y : Nat, x ≤ max' x y ∧ y ≤ max' x y := by
  intro x y
  smt
