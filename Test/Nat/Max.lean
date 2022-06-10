import Smt

def Max (x y : Nat) : Nat := if x ≤ y then y else x

theorem Nat.not_le_of_reverse_le {m n : Nat} : ¬ m ≤ n → n ≤ m := fun hn =>
  match Nat.le_total m n with
  | Or.inl h => absurd h hn
  | Or.inr h => h

theorem Max_ge : ∀ x y : Nat, x ≤ Max x y ∧ y ≤ Max x y := by
  intro x y
  smt
  by_cases h : x ≤ y <;> simp [Max, h]
  apply Nat.not_le_of_reverse_le h

theorem Max_ge' : ∀ x y : Nat, x ≤ Max x y ∧ y ≤ Max x y := by
  intro x y
  smt [Max]
  by_cases h : x ≤ y <;> simp [Max, h]
  apply Nat.not_le_of_reverse_le h
