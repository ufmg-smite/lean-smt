import Smt

-- A proposition `∀ _ : α, p` over a non-`Prop` domain is a quantified formula, not a function
-- type, although its body does not mention the bound variable. It was translated as an arrow
-- sort, `(α -> p)`, which cvc5 rejects ("Symbol '->' not declared as a variable").
theorem forall_non_dependent {α : Type} [Nonempty α] (p : Prop) (h : ∀ _ : α, p) : p := by
  smt [h]

theorem forall_non_dependent_conj {α : Type} [Nonempty α] (q : Prop) (h : q ∧ ∀ _ : α, ¬ False) : q := by
  smt [h]
