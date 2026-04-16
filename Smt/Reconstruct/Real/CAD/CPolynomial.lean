import Mathlib
import CompPoly
import Smt.Reconstruct.Real.CAD.Sturm.SeqDefs

-- Some extensions to CompPoly

namespace CompPoly
namespace CPolynomial

variable {α : Type*}
variable {β : Type*}
variable [BEq α] [LawfulBEq α] [Ring α]
variable [BEq β] [LawfulBEq β] [Ring β]

instance [DecidableEq α] : DecidableEq (CPolynomial α) := Subtype.instDecidableEq

namespace t1

def P : CPolynomial Rat := X ^ 2 - 1
def Q : CPolynomial Rat := X + 1

example : P.div Q = X - 1 := by native_decide

end t1

theorem eval_eq_sum_range : ∀ P : CPolynomial α, ∀ x : α, P.eval x = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * x ^ i := by
  intros P x
  rw [eval_toPoly, natDegree_toPoly]
  have := Polynomial.eval_eq_sum_range (p := P.toPoly) x
  conv =>
    · rhs
      congr
      · skip
      · intro i
        rw [coeff_toPoly]
  rw [this]

theorem eval_toPolyReal_eq_sum_range : ∀ P : CPolynomial Rat, ∀ x : Real, (toPolyReal P).eval x = ∑ i ∈ Finset.range (P.natDegree + 1), (ratToReal (P.coeff i)) * x ^ i := by
  intros P x
  unfold toPolyReal
  simp only [Polynomial.eval_eq_sum_range]
  rw [natDegree_toPoly, Polynomial.natDegree_map ratToRealHom]
  unfold ratToReal
  conv =>
    · rhs
      congr
      · skip
      · intro i
        rw [coeff_toPoly, <- Polynomial.coeff_map]

namespace t2

def P : CPolynomial Rat := X

lemma r1 (a : Rat) : P.eval a = a := by
  rw [eval_eq_sum_range]
  have h1 : P.natDegree = 1 := by native_decide
  have h2 : P.coeff 0 = 0 := by native_decide
  have h3 : P.coeff 1 = 1 := by native_decide
  rw [h1]
  have e1 : ∑ i ∈ {0,1}, P.coeff i * a ^ i = P.coeff 0 * a ^ 0 + P.coeff 1 * a ^ 1 := by grind
  have e2 : Finset.range 2 = {0, 1} := Finset.val_inj.mp rfl
  rw [e2, e1]
  grind

example (a : Rat) : a < 0 → P.eval a < 0 := by
  rw [r1]
  intro h
  exact h

end t2
