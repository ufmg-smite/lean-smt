import Lean
import Qq
import Smt.Reconstruct
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.AlgNum
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Order
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Sign
import Smt.Reconstruct.Real.CAD.RootVal
import Smt.Reconstruct.Real.CAD.Utils
import Smt.Reconstruct.Real.CAD.IS_ROOT_INTRO
import Smt.Reconstruct.Real.CAD.CountRoots

import CompPoly

open Lean Meta Qq CompPoly AlgebraicNumber

lemma eval_ne_zero (q : Rat) (p : CPolynomial Rat) : p.eval q ≠ 0 → (toPolyReal p).eval (ratToReal q) ≠ 0 := by
  intros h1 h2
  unfold toPolyReal ratToReal at h2
  rw [CPolynomial.eval_toPoly] at h1
  have : (↑(p.toPoly.eval q) : Real) ≠ 0 := by finiteness
  rw [eval_comm_map] at this
  simp_all only [ne_eq, eq_ratCast]

theorem seqVarABEquivSturm' (p : CPolynomial ℚ) (a b : ℚ) :
    seqVarSturm_ab (toPolyReal p) (Polynomial.derivative (toPolyReal p)) (ratToReal a) (ratToReal b)
      = seqVarSturmC_ab' p p.derivative a b := by
  have h := seqVarABEquivSturm p 1 a b
  have h1 : toPolyReal (1 : CPolynomial ℚ) = 1 := by
    simp [toPolyReal, CPolynomial.toPoly_one]
  rw [mul_one, h1, mul_one, seqVarSturmC_ab_equiv] at h
  simp only [ratToReal, ratToRealHom, eq_ratCast]
  exact h.symm

theorem seqVarAboveEquivSturm' (p : CPolynomial ℚ) (a : ℚ) :
    seqVarAboveSturm (toPolyReal p) (Polynomial.derivative (toPolyReal p)) (ratToReal a)
      = seqVarAboveSturmC' p p.derivative a := by
  have h := seqVarAboveEquivSturm p 1 a
  have h1 : toPolyReal (1 : CPolynomial ℚ) = 1 := by
    simp [toPolyReal, CPolynomial.toPoly_one]
  rw [mul_one, h1, mul_one, seqVarAboveSturmC_equiv] at h
  simp only [ratToReal, ratToRealHom, eq_ratCast]
  exact h.symm

theorem seqVarBelowEquivSturm' (p : CPolynomial ℚ) (b : ℚ) :
    seqVarBelowSturm (toPolyReal p) (Polynomial.derivative (toPolyReal p)) (ratToReal b)
      = seqVarBelowSturmC' p p.derivative b := by
  have h := seqVarBelowEquivSturm p 1 b
  have h1 : toPolyReal (1 : CPolynomial ℚ) = 1 := by
    simp [toPolyReal, CPolynomial.toPoly_one]
  rw [mul_one, h1, mul_one, seqVarBelowSturmC_equiv] at h
  simp only [ratToReal, ratToRealHom, eq_ratCast]
  exact h.symm

theorem no_roots_between (p : Polynomial ℝ) {lo l r hi : ℝ} (h1 : lo < l) (h2 : l < r) (h3 : r < hi)
    (hl : p.eval l = 0) (hr : p.eval r = 0) (hc : ((rootsInInterval p lo hi).card : ℤ) = 2) :
    ∀ x ∈ Set.Ioo l r, p.eval x ≠ 0 := by
  intro x hx hpx
  -- the count is stated over `ℤ`, as `sturm_interval` produces it
  have hc : (rootsInInterval p lo hi).card = 2 := by exact_mod_cast hc
  -- the zero polynomial has no roots, so `p ≠ 0` and membership is just "root inside the window"
  have hp : p ≠ 0 := by
    rintro rfl
    simp [rootsInIntervalZero] at hc
  have mem : ∀ y, y ∈ rootsInInterval p lo hi ↔ p.eval y = 0 ∧ lo < y ∧ y < hi := by
    intro y
    simp [rootsInInterval, Polynomial.mem_roots hp, Set.mem_Ioo]
  -- `{l, r}` is a two-element subset of a two-element set, hence all of it
  have hsub : ({l, r} : Finset ℝ) ⊆ rootsInInterval p lo hi := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact (mem _).mpr ⟨hl, h1, by linarith⟩
    · exact (mem _).mpr ⟨hr, by linarith, h3⟩
  have heq : ({l, r} : Finset ℝ) = rootsInInterval p lo hi :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair (ne_of_lt h2), hc])
  -- so a root `x` strictly between `l` and `r` would have to be one of them
  have hxmem : x ∈ rootsInInterval p lo hi :=
    (mem x).mpr ⟨hpx, by linarith [hx.1], by linarith [hx.2]⟩
  rw [← heq] at hxmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
  rcases hxmem with rfl | rfl
  · exact lt_irrefl _ hx.1
  · exact lt_irrefl _ hx.2

/-- Half-line `(l, +∞)`: the one root of `p` above `lo` is `l`, so there is none beyond it. -/
theorem no_roots_above (p : Polynomial ℝ) {lo l : ℝ} (h1 : lo < l) (hl : p.eval l = 0)
    (hc : ((Theorem.rootsAbove p lo).card : ℤ) = 1) : ∀ x ∈ Set.Ioi l, p.eval x ≠ 0 := by
  intro x hx hpx
  have hx' : l < x := hx
  have hc : (Theorem.rootsAbove p lo).card = 1 := by exact_mod_cast hc
  have hp : p ≠ 0 := by
    rintro rfl
    simp [Theorem.rootsAbove] at hc
  have mem : ∀ y, y ∈ Theorem.rootsAbove p lo ↔ p.eval y = 0 ∧ lo < y := by
    intro y
    simp [Theorem.rootsAbove, Polynomial.mem_roots hp]
  have hsub : ({l} : Finset ℝ) ⊆ Theorem.rootsAbove p lo := by
    intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    exact (mem _).mpr ⟨hl, h1⟩
  have heq : ({l} : Finset ℝ) = Theorem.rootsAbove p lo :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton, hc])
  have hxmem : x ∈ Theorem.rootsAbove p lo := (mem x).mpr ⟨hpx, by linarith⟩
  rw [← heq, Finset.mem_singleton] at hxmem
  subst hxmem
  exact lt_irrefl _ hx'

/-- Half-line `(-∞, r)`: the one root of `p` below `hi` is `r`, so there is none before it. -/
theorem no_roots_below (p : Polynomial ℝ) {r hi : ℝ} (h3 : r < hi) (hr : p.eval r = 0)
    (hc : ((Theorem.rootsBelow p hi).card : ℤ) = 1) : ∀ x ∈ Set.Iio r, p.eval x ≠ 0 := by
  intro x hx hpx
  have hx' : x < r := hx
  have hc : (Theorem.rootsBelow p hi).card = 1 := by exact_mod_cast hc
  have hp : p ≠ 0 := by
    rintro rfl
    simp [Theorem.rootsBelow] at hc
  have mem : ∀ y, y ∈ Theorem.rootsBelow p hi ↔ p.eval y = 0 ∧ y < hi := by
    intro y
    simp [Theorem.rootsBelow, Polynomial.mem_roots hp]
  have hsub : ({r} : Finset ℝ) ⊆ Theorem.rootsBelow p hi := by
    intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    exact (mem _).mpr ⟨hr, h3⟩
  have heq : ({r} : Finset ℝ) = Theorem.rootsBelow p hi :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton, hc])
  have hxmem : x ∈ Theorem.rootsBelow p hi := (mem x).mpr ⟨hpx, by linarith⟩
  rw [← heq, Finset.mem_singleton] at hxmem
  subst hxmem
  exact lt_irrefl _ hx'

/-- Whole line: a nonzero polynomial with no real roots. -/
theorem no_roots_line (p : Polynomial ℝ) (hp : p ≠ 0) (hc : p.roots.toFinset.card = 0) :
    ∀ x ∈ Set.univ, p.eval x ≠ 0 := by
  intro x _ hpx
  have h : x ∈ p.roots.toFinset := by
    simp [Polynomial.mem_roots hp, hpx]
  rw [Finset.card_eq_zero.mp hc] at h
  exact Finset.notMem_empty x h

/-- On an order-connected set, a continuous function with no zero has constant sign
(intermediate value theorem). -/
private lemma sign_eq_of_no_zero {f : ℝ → ℝ} (hf : Continuous f) {S : Set ℝ} (hS : S.OrdConnected)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≤ y) (h : ∀ z ∈ S, f z ≠ 0) :
    SignType.sign (f x) = SignType.sign (f y) := by
  have hIcc : Set.Icc x y ⊆ S := hS.out hx hy
  rcases lt_trichotomy (f x) 0 with hfx | hfx | hfx
  · rcases lt_trichotomy (f y) 0 with hfy | hfy | hfy
    · rw [sign_neg hfx, sign_neg hfy]
    · exact absurd hfy (h y hy)
    · obtain ⟨z, hz, hz0⟩ :=
        intermediate_value_Icc hxy hf.continuousOn ⟨hfx.le, hfy.le⟩
      exact absurd hz0 (h z (hIcc hz))
  · exact absurd hfx (h x hx)
  · rcases lt_trichotomy (f y) 0 with hfy | hfy | hfy
    · obtain ⟨z, hz, hz0⟩ :=
        intermediate_value_Icc' hxy hf.continuousOn ⟨hfy.le, hfx.le⟩
      exact absurd hz0 (h z (hIcc hz))
    · exact absurd hfy (h y hy)
    · rw [sign_pos hfx, sign_pos hfy]

/-- A polynomial with no root on an order-connected set is sign-invariant there. Covers all the
interval shapes `SGN_INV` uses: `Set.Ioo`, `Set.Ioi`, `Set.Iio` and `Set.univ`. -/
theorem sgnInv_of_no_roots (p : CPolynomial Rat) (S : Set ℝ) (hS : S.OrdConnected)
    (h : ∀ x ∈ S, (toPolyReal p).eval x ≠ 0) : SgnInv p S := by
  unfold SgnInv
  intro x hx y hy
  have hf : Continuous fun z => (toPolyReal p).eval z := (toPolyReal p).continuous
  rcases le_total x y with hxy | hxy
  · exact sign_eq_of_no_zero hf hS hx hy hxy h
  · exact (sign_eq_of_no_zero hf hS hy hx hxy h).symm

/-- The rational expression of a window bound (cvc5 always chooses rational windows). -/
def ratExpr : RootVal → Smt.ReconstructM Q(Rat)
  | .rat e _ => pure e
  | .alg e _ => throwError "[sgn_inv_intro]: expected a rational window bound, got {e}"

/-- The window bound next to a finite end of the piece (an infinite window end only accompanies
an infinite end of the piece). -/
def windowBound : Option RootVal → Smt.ReconstructM RootVal
  | some b => pure b
  | none => throwError "[sgn_inv_intro]: missing rational window bound next to a finite endpoint"

/-- Reconstructs `SGN_INV_INTRO(p, l, r, lo, hi)`: proves `SgnInv p S` for the open piece `(l, r)`
(`none` for an infinite end), from the rational window `(lo, hi)` around it in which the only
roots of `p` are the finite ends. -/
def sgn_inv_intro_core (p : Q(CPolynomial Rat)) (p_native : CPolynomial Rat) (l r : Option RootVal) (lo hi : Option RootVal) : Smt.ReconstructM Expr := do
  match l, r with
  | none, none =>
    -- whole line: `p ≠ 0` and no real roots at all
    let p_real : Q(Polynomial ℝ) := q(toPolyReal $p)
    let pf_p_ne_0 ← mkDecideProof' q($p ≠ 0)
    let pf_p_ne_0 ← mkAppM ``toPolyReal_zero #[p, pf_p_ne_0]
    let pf_count ← gen_root_counting_proof p p_native
    let no_roots ← mkAppM ``no_roots_line #[p_real, pf_p_ne_0, pf_count]
    let S : Q(Set Real) := q(Set.univ)
    let hS : Q(Set.OrdConnected $S) := q(Set.ordConnected_univ)
    mkAppM ``sgnInv_of_no_roots #[p, S, hS, no_roots]
  | some l, none =>
    -- half-line `(l, +∞)`: exactly one root of `p` above `lo`, namely `l`
    let p_real : Q(Polynomial ℝ) := q(toPolyReal $p)
    let lo_rv ← windowBound lo
    let lo : Q(Rat) ← ratExpr lo_rv
    let pf_p_lo_ne_0 ← mkDecideProof' q(CPolynomial.eval $lo $p ≠ 0)
    let pf_p_lo_ne_0 ← mkAppM ``eval_ne_zero #[lo, p, pf_p_lo_ne_0]
    let p_der : Q(CPolynomial Rat) ← mkAppM ``CPolynomial.derivative #[p]
    let pf_var_eq_1 ← mkDecideProof' q(seqVarAboveSturmC' $p $p_der $lo = 1)
    let pf_var_eq_var ← mkAppM ``seqVarAboveEquivSturm' #[p, lo]
    let pf_var_eq_1' ← mkAppM ``Eq.trans #[pf_var_eq_var, pf_var_eq_1]
    let sturm_p ← mkAppM ``Theorem.sturm_above #[q(ratToReal $lo), p_real, pf_p_lo_ne_0]
    let pf_one_root ← mkAppM ``Eq.trans #[sturm_p, pf_var_eq_1']
    let lR : Q(Real) ← l.toReal
    let p_root_l ← mkExpectedTypeHint (← get_is_root_pf p p_native l) q(Polynomial.eval $lR $p_real = 0)
    let pf_lo_lt_l ← gen_toReal_lt lo_rv l
    let no_roots ← mkAppM ``no_roots_above #[p_real, pf_lo_lt_l, p_root_l, pf_one_root]
    let S : Q(Set Real) := q(Set.Ioi $lR)
    let hS : Q(Set.OrdConnected $S) := q(Set.ordConnected_Ioi)
    mkAppM ``sgnInv_of_no_roots #[p, S, hS, no_roots]
  | none, some r =>
    -- half-line `(-∞, r)`: exactly one root of `p` below `hi`, namely `r`
    let p_real : Q(Polynomial ℝ) := q(toPolyReal $p)
    let hi_rv ← windowBound hi
    let hi : Q(Rat) ← ratExpr hi_rv
    let pf_p_hi_ne_0 ← mkDecideProof' q(CPolynomial.eval $hi $p ≠ 0)
    let pf_p_hi_ne_0 ← mkAppM ``eval_ne_zero #[hi, p, pf_p_hi_ne_0]
    let p_der : Q(CPolynomial Rat) ← mkAppM ``CPolynomial.derivative #[p]
    let pf_var_eq_1 ← mkDecideProof' q(seqVarBelowSturmC' $p $p_der $hi = 1)
    let pf_var_eq_var ← mkAppM ``seqVarBelowEquivSturm' #[p, hi]
    let pf_var_eq_1' ← mkAppM ``Eq.trans #[pf_var_eq_var, pf_var_eq_1]
    let sturm_p ← mkAppM ``Theorem.sturm_below #[q(ratToReal $hi), p_real, pf_p_hi_ne_0]
    let pf_one_root ← mkAppM ``Eq.trans #[sturm_p, pf_var_eq_1']
    let rR : Q(Real) ← r.toReal
    let p_root_r ← mkExpectedTypeHint (← get_is_root_pf p p_native r) q(Polynomial.eval $rR $p_real = 0)
    let pf_r_lt_hi ← gen_toReal_lt r hi_rv
    let no_roots ← mkAppM ``no_roots_below #[p_real, pf_r_lt_hi, p_root_r, pf_one_root]
    let S : Q(Set Real) := q(Set.Iio $rR)
    let hS : Q(Set.OrdConnected $S) := q(Set.ordConnected_Iio)
    mkAppM ``sgnInv_of_no_roots #[p, S, hS, no_roots]
  | some l, some r =>
    let p_real : Q(Polynomial ℝ) := q(toPolyReal $p)
    let lo_rv ← windowBound lo
    let hi_rv ← windowBound hi
    let lo_q : Q(Rat) ← ratExpr lo_rv
    let hi_q : Q(Rat) ← ratExpr hi_rv
    let lo := lo_q
    let hi := hi_q
    let pf_p_lo_ne_0 ← mkDecideProof' q(CPolynomial.eval $lo $p ≠ 0)
    let pf_p_lo_ne_0 : Q(Polynomial.eval (ratToReal $lo) $p_real ≠ 0) ← mkAppM ``eval_ne_zero #[lo, p, pf_p_lo_ne_0]
    let pf_p_hi_ne_0 ← mkDecideProof' q(CPolynomial.eval $hi $p ≠ 0)
    let pf_p_hi_ne_0 : Q(Polynomial.eval (ratToReal $hi) $p_real ≠ 0) ← mkAppM ``eval_ne_zero #[hi, p, pf_p_hi_ne_0]
    let pf_lo_lt_hi ← mkDecideProof' q($lo < $hi)
    let pf_lo_lt_hi : Q(ratToReal $lo < ratToReal $hi) ← mkAppM ``ratToReal_lt #[lo, hi, pf_lo_lt_hi]
    let p_der : Q(CPolynomial Rat) ← mkAppM ``CPolynomial.derivative #[p]
    let pf_var_eq_2 ← mkDecideProof' q(seqVarSturmC_ab' $p $p_der $lo $hi = 2)
    let pf_var_eq_var ← mkAppM ``seqVarABEquivSturm' #[p, lo, hi]
    let pf_var_eq_2' ← mkAppM ``Eq.trans #[pf_var_eq_var, pf_var_eq_2]
    let sturm_p ←
      mkAppM ``Theorem.sturm_interval #[q(ratToReal $lo), q(ratToReal $hi), p_real, pf_lo_lt_hi, pf_p_lo_ne_0, pf_p_hi_ne_0]
    let pf_two_roots ← mkAppM ``Eq.trans #[sturm_p, pf_var_eq_2']
    -- endpoint facts: `l` and `r` are roots of `p`
    let lR : Q(Real) ← l.toReal
    let rR : Q(Real) ← r.toReal
    let p_root_l ← mkExpectedTypeHint (← get_is_root_pf p p_native l) q(Polynomial.eval $lR $p_real = 0)
    let p_root_r ← mkExpectedTypeHint (← get_is_root_pf p p_native r) q(Polynomial.eval $rR $p_real = 0)
    -- order facts: lo < l < r < hi
    let pf_lo_lt_l ← gen_toReal_lt lo_rv l
    let pf_l_lt_r ← gen_toReal_lt l r
    let pf_r_lt_hi ← gen_toReal_lt r hi_rv
    -- the two roots counted in the window are the endpoints, so `(l, r)` is root-free
    let no_roots ← mkAppM ``no_roots_between
      #[p_real, pf_lo_lt_l, pf_l_lt_r, pf_r_lt_hi, p_root_l, p_root_r, pf_two_roots]
    -- hence `p` is sign-invariant on `(l, r)`
    let S : Q(Set Real) := q(Set.Ioo $lR $rR)
    let hS : Q(Set.OrdConnected $S) := q(Set.ordConnected_Ioo)
    mkAppM ``sgnInv_of_no_roots #[p, S, hS, no_roots]
