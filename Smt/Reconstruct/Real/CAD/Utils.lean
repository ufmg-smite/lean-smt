import Mathlib
import Lean
import CompPoly

open Lean Elab Tactic ToExpr Meta

def simp' (mvarId : MVarId) (hs : List Expr) : MetaM MVarId := mvarId.withContext do
  let congrTheorems ← getSimpCongrTheorems
  let simpTheorems ← getSimpTheorems
  let mut simpTheoremsArray : SimpTheoremsArray := #[simpTheorems]
  for h in hs do
    simpTheoremsArray ← SimpTheoremsArray.addTheorem simpTheoremsArray (.other `h) h
  let simprocs ← Simp.getSimprocs
  let ctx ← Simp.mkContext (simpTheorems := simpTheoremsArray) (congrTheorems := congrTheorems)
  let (result?, _) ← simpTarget mvarId ctx (simprocs := #[simprocs])
  return result?.get!

def rewriteMVar (mvarId : MVarId) (eqProof : Expr) : MetaM MVarId :=
  mvarId.withContext do
    let tgt    ← mvarId.getType
    let result ← mvarId.rewrite tgt eqProof
    let newMVar ← mkFreshExprSyntheticOpaqueMVar result.eNew
    mvarId.assign (← mkEqMPR result.eqProof newMVar)
    return newMVar.mvarId!

/-- Given:
  - `h1 : P`  (a proof of some proposition)
  - `h2 : a = b`  (a proof of some equality)
  Produces `h1' : P[a ↦ b]`, i.e. `h1` rewritten left-to-right by `h2` everywhere. -/
def rewriteWithEq (h1 h2 : Expr) : MetaM Expr := do
  let prop ← inferType h1
  let eqType ← inferType h2
  let some (α, a, b) := eqType.eq?
    | throwError "rewriteWithEq: h2 is not a proof of an equality, got {eqType}"
  let motive ← kabstract prop a
  if motive == prop then
    return h1
  let newProp := motive.instantiate1 b
  let motiveExpr := mkLambda `x .default α motive
  let h1' ← mkAppOptM ``Eq.subst #[none, motiveExpr, a, b, h2, h1]
  let h1'Type ← inferType h1'
  unless ← isDefEq h1'Type newProp do
    throwError "rewriteWithEq: type mismatch, expected {newProp} but got {h1'Type}"
  return h1'

lemma list_eq_of_sorted_of_length_of_mem (l1 l2 : List Real) : l1.length = l2.length → (∀ i ∈ l1, i ∈ l2) → l1.SortedLT → l2.SortedLT → l1 = l2 := by
  intros hlen h1 h2 h3
  have nd1 := h2.nodup
  have nd2 := h3.nodup
  have hcard : l1.toFinset.card = l2.toFinset.card := by
    rw [List.toFinset_card_of_nodup nd1, List.toFinset_card_of_nodup nd2, hlen]
  have hsub : l1.toFinset ⊆ l2.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact h1 x hx
  have hfeq : l1.toFinset = l2.toFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard.ge
  have hperm := List.perm_of_nodup_nodup_toFinset_eq nd1 nd2 hfeq
  exact hperm.eq_of_sortedLE h2.sortedLE h3.sortedLE

theorem no_roots_between_roots (p : Polynomial ℝ) (hp : p ≠ 0) : ∀ i < (p.roots.toFinset.sort (· ≤ ·)).length - 1,
  ¬∃ x : ℝ , x ∈ Set.Ioo (p.roots.toFinset.sort (· ≤ ·))[i]! (p.roots.toFinset.sort (· ≤ ·))[i+1]! ∧ p.eval x = 0 := by
  intro i hi
  by_contra h
  obtain ⟨x, ⟨hxi, hxi1⟩, hx_root⟩ := h
  have h_roots : x ∈ p.roots := by simp_all
  have hx_mem_sorted : x ∈ p.roots.toFinset.sort (· ≤ ·) := by simpa using h_roots
  have F := (List.exists_mem_iff_getElem (l := p.roots.toFinset.sort) (p := fun y => y = x)).mp (by use x)
  obtain ⟨j, hj⟩ : ∃ j : Fin ((p.roots.toFinset.sort (· ≤ ·)).length), x = (p.roots.toFinset.sort (· ≤ ·))[j] := by
    simp at F
    obtain ⟨i, ⟨h1, h2⟩⟩ := F
    have : p.roots.toFinset.card = p.roots.toFinset.sort.length := Eq.symm (Finset.length_sort fun a b => a ≤ b)
    use ⟨i, by grind⟩
    grind
  have contr1 : j > i := by
    by_contra h
    rw[hj] at hxi1
    have hmono :
      (p.roots.toFinset.sort (· ≤ ·))[i] ≥
      (p.roots.toFinset.sort (· ≤ ·))[j] := by
      simp_all only [Fin.getElem_fin]
      have hsorted2 : (p.roots.toFinset.sort (· ≤ ·)).SortedLT := Finset.sortedLT_sort p.roots.toFinset
      apply (StrictMono.le_iff_le (Finset.sortedLT_sort p.roots.toFinset)).mpr
      grind
    have hcontra : (p.roots.toFinset.sort (· ≤ ·))[j] < (p.roots.toFinset.sort (· ≤ ·))[j] := by
      simp_all
      grind
    exact lt_irrefl _ hcontra
  have contr2 : j < i + 1 := by
    by_contra h
    rw[hj] at hxi1
    have hmono :
      (p.roots.toFinset.sort (· ≤ ·))[i+1] ≤
      (p.roots.toFinset.sort (· ≤ ·))[j] := by
      simp_all only [Fin.getElem_fin]
      have hsorted2 : (p.roots.toFinset.sort (· ≤ ·)).SortedLT := Finset.sortedLT_sort p.roots.toFinset
      apply (StrictMono.le_iff_le (Finset.sortedLT_sort p.roots.toFinset)).mpr
      grind
    have hcontra : (p.roots.toFinset.sort (· ≤ ·))[j] < (p.roots.toFinset.sort (· ≤ ·))[j] := by grind
    exact lt_irrefl _ hcontra
  linarith

open CompPoly

theorem gneg_imp_gtopoly_neg (g : CPolynomial ℚ) (h : g ≠ 0) : g.toPoly ≠ 0 := by
  intro abs
  have : g = 0 := by
    apply CPolynomial.eq_zero_iff_coeff_zero.mpr
    have aux (x : ℚ) := CPolynomial.eval_toPoly x g
    rw[abs] at aux
    simp at aux
    simp only [CPolynomial.coeff_toPoly]
    rw[abs]
    apply Polynomial.coeff_zero
  exact h this

theorem gtopolyzeroeq2 (g : CPolynomial ℚ) : g.toPoly ≠ 0 → g ≠ 0 := by
  contrapose
  intro h; rw[h]; exact CPolynomial.toPoly_zero

theorem gtopolyzeroeq (g : CPolynomial ℚ) : g.toPoly = 0 → g = 0 := by
  contrapose
  apply gneg_imp_gtopoly_neg

theorem fg_mod_eq (f g : CPolynomial ℚ) : (f % g).toPoly = f.toPoly % g.toPoly := by
  have aux := CPolynomial.mod_toPoly f g
  have : (f.mod g) = f%g := CPolynomial.eq_iff_coeff.mpr (congrFun rfl)
  rw[this] at aux
  apply aux

@[grind =]
noncomputable def toPolyReal (p : CPolynomial Rat) : Polynomial Real := p.toPoly.map (Rat.castHom Real)

open CompPoly in
lemma toPolyReal_zero (p : CPolynomial Rat) : p ≠ 0 → toPolyReal p ≠ 0 := by
  intros h
  exact Polynomial.map_ne_zero (gneg_imp_gtopoly_neg p h)

theorem gneg_imp_gtopoly_neg' (g : CPolynomial ℚ) (h : g ≠ 0) : g.toPoly ≠ 0 := by
  intro abs
  have : g = 0 := by
    apply CPolynomial.eq_zero_iff_coeff_zero.mpr
    have aux (x : ℚ) := CPolynomial.eval_toPoly x g
    rw[abs] at aux
    simp at aux
    simp only [CPolynomial.coeff_toPoly]
    rw[abs]
    apply Polynomial.coeff_zero
  exact h this

theorem gtopolyzeroeq2' (g : CPolynomial ℚ) : g.toPoly ≠ 0 → g ≠ 0 := by
  contrapose
  intro h; rw[h]; exact CPolynomial.toPoly_zero

theorem gtopolyzeroeq' (g : CPolynomial ℚ) : g.toPoly = 0 → g = 0 := by
  contrapose
  apply gneg_imp_gtopoly_neg

