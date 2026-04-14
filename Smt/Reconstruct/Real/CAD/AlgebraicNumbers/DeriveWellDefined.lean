import Lean
import Mathlib
import CompPoly
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.AlgNum
import Smt.Reconstruct.Real.CAD.Sturm.Decidable

open Qq Lean Elab Tactic Meta
open CompPoly
open AlgebraicNumber

/-
This file defines a metaprogram that receives the data of an algebraic number
(`AlgebraicNumber.Raw`) and lifts it into an `AlgNum`, assuming it is well defined.
-/

theorem wellDefined_iff_rootsInInterval (a : Raw)
    (hp : toPolyReal a.p ≠ 0)
    (hl : a.p.eval a.l ≠ 0)
    (hr : a.p.eval a.r ≠ 0)
    (hlr : a.l < a.r) :
    a.wellDefined ↔
      Finset.card (rootsInInterval (a.p.toPoly.map ratToRealHom) ↑a.l ↑a.r) = 1 := by
  set q := a.p.toPoly.map ratToRealHom with hq_def
  obtain ⟨p, l, r⟩ := a
  simp only at *
  rw [CPolynomial.eval_toPoly] at hl hr
  have hl' : Polynomial.eval (↑l : ℝ) q ≠ 0 := by
    rw [hq_def, ← eval_comm_map]; exact_mod_cast hl
  have hr' : Polynomial.eval (↑r : ℝ) q ≠ 0 := by
    rw [hq_def, ← eval_comm_map]; exact_mod_cast hr
  have hlr' : (l : ℝ) < r := Rat.cast_lt.mpr hlr
  have eval_conv : ∀ x : ℝ, (toPolyReal p).eval x = q.eval x := by
    intro x; unfold toPolyReal; gcongr
  constructor
  · rintro ⟨x, ⟨hxeval, hxl, hxr⟩, hx_unique⟩
    have hxl' : (↑l : ℝ) < x := by
      rcases eq_or_lt_of_le hxl with heq | hlt
      · exfalso; exact hl' (by rw [← eval_conv, heq]; exact hxeval)
      · exact hlt
    have hxr' : x < (↑r : ℝ) := by
      rcases eq_or_lt_of_le hxr with heq | hlt
      · exfalso; exact hr' (by rw [← eval_conv, ← heq]; exact hxeval)
      · exact hlt
    have hx_root : q.eval x = 0 := by rwa [← eval_conv]
    have hx_mem : x ∈ rootsInInterval q ↑l ↑r := by
      simp only [rootsInInterval, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots',
        Polynomial.IsRoot.def]
      exact ⟨⟨hp, hx_root⟩, Set.mem_Ioo.mpr ⟨hxl', hxr'⟩⟩
    suffices rootsInInterval q ↑l ↑r = {x} by rw [this, Finset.card_singleton]
    ext y
    simp only [Finset.mem_singleton]
    constructor
    · intro hy
      simp only [rootsInInterval, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots',
        Polynomial.IsRoot.def] at hy
      obtain ⟨⟨_, hy_root⟩, hy_ioo⟩ := hy
      have hy_ioo := Set.mem_Ioo.mp hy_ioo
      apply hx_unique
      exact ⟨by rw [eval_conv]; exact hy_root, le_of_lt hy_ioo.1, le_of_lt hy_ioo.2⟩
    · rintro rfl; exact hx_mem
  · intro hcard
    rw [Finset.card_eq_one] at hcard
    obtain ⟨x, hx_eq⟩ := hcard
    have hx_mem : x ∈ rootsInInterval q ↑l ↑r := by
      rw [hx_eq]; exact Finset.mem_singleton_self x
    simp only [rootsInInterval, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots',
      Polynomial.IsRoot.def] at hx_mem
    obtain ⟨⟨_, hx_root⟩, hx_ioo⟩ := hx_mem
    have hx_ioo := Set.mem_Ioo.mp hx_ioo
    refine ⟨x, ⟨by rw [eval_conv]; exact hx_root, le_of_lt hx_ioo.1, le_of_lt hx_ioo.2⟩, ?_⟩
    intro y ⟨hyeval, hyl, hyr⟩
    have hyl' : (↑l : ℝ) < y := by
      rcases eq_or_lt_of_le hyl with heq | hlt
      · exfalso; exact hl' (by rw [← eval_conv, heq]; exact hyeval)
      · exact hlt
    have hyr' : y < (↑r : ℝ) := by
      rcases eq_or_lt_of_le hyr with heq | hlt
      · exfalso; exact hr' (by rw [← eval_conv, ← heq]; exact hyeval)
      · exact hlt
    have hy_root : q.eval y = 0 := by rwa [← eval_conv]
    have hy_mem : y ∈ rootsInInterval q ↑l ↑r := by
      simp only [rootsInInterval, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots',
        Polynomial.IsRoot.def]
      exact ⟨⟨hp, hy_root⟩, Set.mem_Ioo.mpr ⟨hyl', hyr'⟩⟩
    rw [hx_eq] at hy_mem
    exact Finset.mem_singleton.mp hy_mem

lemma sturm_l_r_cpoly (p : CPolynomial ℚ) (l r : ℚ) (hl : p.eval l ≠ 0) (hr : p.eval r ≠ 0) (hlr : l < r) :
    seqVarSturmC_ab' p p.derivative l r = (rootsInInterval (p.toPoly.map ratToRealHom) l r).card := by
  rw [<- seqVarSturmC_ab_equiv]
  have : p.derivative = p.derivative * 1 := by norm_num
  rw [this, seqVarABEquivSturm p 1]
  have hl0 : Polynomial.eval (↑l) (Polynomial.map ratToRealHom p.toPoly) ≠ 0 := by
    rw [<- cpolynomial_map_cast l p]
    finiteness
  have hr0 : Polynomial.eval (↑r) (Polynomial.map ratToRealHom p.toPoly) ≠ 0 := by
    rw [<- cpolynomial_map_cast r p]
    finiteness
  have sturm_l_r := Theorem.sturm_interval l r (p.toPoly.map ratToRealHom) (Real.ratCast_lt.mpr hlr) hl0 hr0
  have : (Polynomial.derivative (Polynomial.map ratToRealHom p.toPoly) * Polynomial.map ratToRealHom (CPolynomial.toPoly 1))
       = (Polynomial.derivative (Polynomial.map ratToRealHom p.toPoly)) := by
    rw [CPolynomial.toPoly_one, Polynomial.map_one ratToRealHom]
    norm_num
  unfold toPolyReal
  rw [this, sturm_l_r]

def AlgNum.mk
    (a : Raw)
    (hp : a.p ≠ 0)
    (hl : a.p.eval a.l ≠ 0)
    (hr : a.p.eval a.r ≠ 0)
    (hlr : a.l < a.r)
    (hsgn : a.sgnDiff)
    (h_int : seqVarSturmC_ab' a.p a.p.derivative a.l a.r = 1) : AlgNum :=
  have h0 : a.p.toPoly.map ratToRealHom ≠ 0 := Polynomial.map_ne_zero (gneg_imp_gtopoly_neg a.p hp)
  have h_roots : Finset.card (rootsInInterval (a.p.toPoly.map ratToRealHom) ↑a.l ↑a.r) = 1 := by
    zify
    rw [<- sturm_l_r_cpoly a.p a.l a.r hl hr hlr]
    exact h_int
  have h1 : a.wellDefined := (wellDefined_iff_rootsInInterval a h0 hl hr hlr).mpr h_roots
  ⟨a, And.intro h1 hsgn⟩

instance (a : Raw) : Decidable a.sgnDiff := by
  unfold Raw.sgnDiff
  exact (CPolynomial.eval a.l a.p * CPolynomial.eval a.r a.p).instDecidableLe 0

syntax (name := lift_alg_num) "lift_alg_num" term : tactic

def Raw.lift (r : Q(Raw)) : MetaM Q(AlgNum) := do
  let g1 : Q(Prop) := q(Raw.p $r ≠ 0)
  let pf1 : Q($g1) ← mkDecideProof g1
  let g2 : Q(Prop) := q((Raw.p $r).eval (Raw.l $r) ≠ 0)
  let pf2 : Q($g2) ← mkDecideProof g2
  let g3 : Q(Prop) := q((Raw.p $r).eval (Raw.r $r) ≠ 0)
  let pf3 : Q($g3) ← mkDecideProof g3
  let g4 : Q(Prop) := q((Raw.l $r) < (Raw.r $r))
  let pf4 : Q($g4) ← mkDecideProof g4
  let g5 : Q(Prop) := q(Raw.sgnDiff $r)
  let pf5 : Q($g5) ← mkDecideProof g5
  let g6 : Q(Prop) := q(seqVarSturmC_ab' (Raw.p $r) (Raw.p $r).derivative (Raw.l $r) (Raw.r $r) = 1)
  let pf6 : Q($g6) ← mkDecideProof g6
  return q(AlgNum.mk $r $pf1 $pf2 $pf3 $pf4 $pf5 $pf6)

@[tactic lift_alg_num] def evalLiftAlgNum : Tactic := fun stx => withMainContext do
  let r: Q(Raw) ← elabTerm stx[1] none
  let a: Q(AlgNum) ← Raw.lift r
  closeMainGoal .anonymous a

namespace tests

def p : CPolynomial Rat := CPolynomial.X + CPolynomial.C 1
def r : Raw := ⟨p, -5, 5⟩

-- <10*x^2 + 2*x + (-15), (-3/2, -5/4)>
open CPolynomial
def p' : CPolynomial Rat := (-15) + 3 * X + 10  * (X)^2
def r': Raw := ⟨p', -3/2, -5/4⟩

def a : AlgNum := by lift_alg_num r
def a' : AlgNum := by lift_alg_num r'
#check a'
#check a
#eval a.l
#eval a.p.eval 3
#print axioms a

end tests
