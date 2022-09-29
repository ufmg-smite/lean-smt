import Meta.Boolean
import Meta.Resolution

theorem mpCvc5 (P Q : Prop) : ¬ (P → (P → Q) → Q) → False :=
  λ lean_a0 =>
    have lean_s0     := notImplies2 lean_a0
    have lean_s1     := notImplies1 lean_s0
    have lean_s2     := impliesElim lean_s1
    have lean_s4     := notImplies1 lean_a0
    have lean_s6     := by resolution_1 lean_s4, lean_s2, P
    have lean_s9     := notImplies2 lean_s0
    contradiction lean_s6 lean_s9

theorem mp : ∀ (P Q : Prop), P → (P → Q) → Q := λ P Q => doubleNeg (mpCvc5 P Q)
