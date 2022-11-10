
import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.Resolution

example : y = a ∨ ¬x = a ∨ ¬x = b ∨ ¬y = b → y = b ∨ ¬(x = b ∧ y = b) → y = a ∨ ¬x = a ∨ ¬x = b ∨ ¬(x = b ∧ y = b) := by
  intros lean_s39 lean_s7
  R2 lean_s39, lean_s7, (Eq y b)

