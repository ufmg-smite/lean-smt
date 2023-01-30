import Lean

initialize
  Lean.registerTraceClass `smt.profile

theorem binderCongr {p q : Prop} : (p = q) → (forall _: Prop, p) = forall _: Prop, q := by
  intro h
  rw [h]

