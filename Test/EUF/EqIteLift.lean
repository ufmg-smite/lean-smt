import Smt

-- `EQ_ITE_LIFT` must reconstruct the `ite` condition as a `Prop`. Reconstructing it as a `Bool`
-- produced `(c = x) = true`, which the kernel rejected even though `smt` reported success.
theorem eq_ite_lift {α γ : Type} [Nonempty α] [Nonempty γ] [DecidableEq α]
    (f : α → γ) (v : γ) (c : α) :
    (∃ x, (if c = x then v else f x) ≠ v) → ∃ x, f x ≠ v := by
  smt
