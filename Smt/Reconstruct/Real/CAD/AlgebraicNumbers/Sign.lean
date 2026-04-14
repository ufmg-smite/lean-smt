import Lean
import Mathlib
import CompPoly
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.DeriveWellDefined
import Smt.Reconstruct.Real.CAD.Sturm.Decidable

open AlgebraicNumber
open CompPoly

lemma root_in_refineN (α : AlgNum) (x : ℝ) (hx : (toPolyReal α.p).eval x = 0)
    (hxl : ↑α.l ≤ x) (hxr : x ≤ ↑α.r) (n : ℕ) :
    ↑(AlgNum.refine^[n] α).l ≤ x ∧ x ≤ ↑(AlgNum.refine^[n] α).r := by
  induction n with
  | zero => exact ⟨hxl, hxr⟩
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp]
    set β := AlgNum.refine^[n] α
    have hβp : β.p = α.p := AlgNum.refineN_p α n
    have hwd := β.isWellDefined
    rw [AlgNum.wellDefined, hβp] at hwd
    obtain ⟨y, ⟨hy_root, hy_l, hy_r⟩, hy_unique⟩ := hwd
    have hxy : x = y := hy_unique x ⟨hx, ih.1, ih.2⟩
    have hβrp : β.refine.p = α.p := by rw [AlgNum.refine_p, hβp]
    have hwd' := β.refine.isWellDefined
    rw [AlgNum.wellDefined, hβrp] at hwd'
    obtain ⟨z, ⟨hz_root, hz_l, hz_r⟩, hz_unique⟩ := hwd'
    have hz_in_β : ↑β.l ≤ z ∧ z ≤ ↑β.r := by
      constructor
      · exact le_trans (by exact_mod_cast β.refine_bounds_l) hz_l
      · exact le_trans hz_r (by exact_mod_cast β.refine_bounds_r)
    have hzy : z = y := hy_unique z ⟨hz_root, hz_in_β.1, hz_in_β.2⟩
    rw [hxy, ← hzy]
    exact ⟨hz_l, hz_r⟩

lemma toReal_in_refineN (α : AlgNum) (n : ℕ) :
    ↑(AlgNum.refine^[n] α).l ≤ α.toReal ∧ α.toReal ≤ ↑(AlgNum.refine^[n] α).r := by
  have key : α.toReal = (AlgNum.refine^[n] α).toReal := by
    induction n with
    | zero => simp
    | succ n ih => rw [ih, Function.iterate_succ', Function.comp, refine_toReal]
  rw [key]
  exact toReal_bounds _

lemma wellDefined_root (α : AlgNum) (x : ℝ) (hx_l : α.l ≤ x) (hx_r : x ≤ α.r) (hx_root : (toPolyReal α.p).eval x = 0) : α.toReal = x := by
  by_contra hne
  have hne' : α.toReal - x ≠ 0 := sub_ne_zero.mpr hne
  have habs_pos : |α.toReal - x| > 0 := abs_pos.mpr hne'
  have hlr := α.lr
  have hwidth_nn : (0 : ℝ) ≤ (↑α.r : ℝ) - ↑α.l := by
    have : (↑α.l : ℝ) ≤ ↑α.r := by exact_mod_cast hlr
    linarith
  suffices ∀ n : ℕ, |α.toReal - x| ≤ ((↑α.r : ℝ) - ↑α.l) / 2 ^ n by
    rcases eq_or_lt_of_le hwidth_nn with heq | hlt
    · specialize this 0
      simp only [pow_zero, div_one] at this
      linarith [heq.symm]
    · have hdiv_pos : 0 < |α.toReal - x| / ((↑α.r : ℝ) - ↑α.l) := div_pos habs_pos hlt
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hdiv_pos (show (1:ℝ)/2 < 1 by norm_num)
      have h := this N
      have h2pos : (0 : ℝ) < 2 ^ N := pow_pos (by norm_num : (0:ℝ) < 2) N
      have key : ((↑α.r : ℝ) - ↑α.l) / 2 ^ N < |α.toReal - x| := by
        have hmul := mul_lt_mul_of_pos_left hN hlt
        rw [mul_div_cancel₀ _ (ne_of_gt hlt)] at hmul
        rwa [one_div, inv_pow, ← div_eq_mul_inv] at hmul
      linarith
  intro n
  have h_toReal := toReal_in_refineN α n
  have h_x := root_in_refineN α x hx_root hx_l hx_r n
  have h_width := refineN_width α n
  have h_width_real : (↑(AlgNum.refine^[n] α).r : ℝ) - ↑(AlgNum.refine^[n] α).l =
      ((↑α.r : ℝ) - ↑α.l) / 2 ^ n := by
    have : ((AlgNum.refine^[n] α).r : ℝ) - (AlgNum.refine^[n] α).l =
        ((α.r : ℝ) - α.l) / 2 ^ n := by exact_mod_cast h_width
    exact this
  rw [abs_le]
  constructor <;> nlinarith [h_toReal.1, h_toReal.2, h_x.1, h_x.2]

lemma toReal_root (α : AlgNum) : (toPolyReal α.p).eval α.toReal = 0 := by
  obtain ⟨x, ⟨hx_root, hx_l, hx_r⟩, _⟩ := α.isWellDefined
  suffices h : α.toReal = x by rw [h]; exact hx_root
  exact wellDefined_root α x hx_l hx_r hx_root

lemma toReal_in_rootsInInterval (α : AlgNum) (hpl : α.p.eval α.l ≠ 0) (hpr : α.p.eval α.r ≠ 0) :
    α.toReal ∈ rootsInInterval (toPolyReal α.p) α.l α.r := by
  simp [toPolyReal, rootsInInterval]
  refine And.intro (And.intro ?_ ?_) (And.intro ?_ ?_)
  · intro abs
    have : α.p = 0 := gtopolyzeroeq' α.p abs
    rw [this] at hpl
    exact false_of_ne hpl
  · exact toReal_root α
  · have hl_leq := (toReal_bounds α).1
    apply Std.lt_of_le_of_ne hl_leq ?_
    intro abs
    have := toReal_root α
    rw [<- abs] at this
    rw [CPolynomial.eval_toPoly, <- (Rat.cast_ne_zero (α := Real)), eval_comm_map] at hpl
    exact hpl this
  · have hr_leq := (toReal_bounds α).2
    apply Std.lt_of_le_of_ne hr_leq ?_
    intro abs
    have := toReal_root α
    rw [abs] at this
    rw [CPolynomial.eval_toPoly, <- (Rat.cast_ne_zero (α := Real)), eval_comm_map] at hpr
    exact hpr this

lemma toReal_only_root (α : AlgNum) (hpl: α.p.eval α.l ≠ 0) (hpr: α.p.eval α.r ≠ 0) :
    rootsInInterval (toPolyReal α.p) α.l α.r = {α.toReal} := by
  set S := rootsInInterval (toPolyReal α.p) α.l α.r
  have h1 : α.toReal ∈ S := toReal_in_rootsInInterval α hpl hpr
  have h2 : ∀ y ∈ S, y = α.toReal := by
    have := α.isWellDefined
    obtain ⟨x, ⟨⟨hx1, hx2, hx3⟩, hx4⟩⟩ := this
    have : α.toReal = x := wellDefined_root α x hx2 hx3 hx1
    intros y hy
    simp [S, rootsInInterval] at hy
    obtain ⟨⟨_, h_root⟩, ⟨hyl, hyr⟩⟩ := hy
    rw [this]
    apply hx4
    exact And.intro h_root (And.intro (le_of_lt hyl) (le_of_lt hyr))
  grind

lemma sgn_eval_alg (q : CPolynomial Rat) (α : AlgNum) (hpl: α.p.eval α.l ≠ 0) (hpr: α.p.eval α.r ≠ 0) :
    sgn ((toPolyReal q).eval α.toReal) =
    ∑ x ∈ rootsInInterval (toPolyReal α.p) α.l α.r, sgn ((toPolyReal q).eval x) := by
  rw [toReal_only_root α hpl hpr]
  simp

lemma AlgNum.lr' (α : AlgNum) (hl : α.p.eval α.l ≠ 0) : α.l < α.r := by
  have := α.lr
  apply Std.lt_of_le_of_ne this
  intro abs
  have hr : α.p.eval α.r ≠ 0 := by rw [<- abs]; exact hl
  have := α.hasSgnDiff
  unfold AlgNum.sgnDiff at this
  rw [abs] at this
  have := mul_self_pos.mpr hr
  linarith

lemma sgn_eval_alg_sturm_seq (q : CPolynomial Rat) (α : AlgNum) (hpl: α.p.eval α.l ≠ 0) (hpr: α.p.eval α.r ≠ 0) :
    sgn ((toPolyReal q).eval α.toReal) = seqVarSturmC_ab' α.p (α.p.derivative * q) α.l α.r := by
  rw [sgn_eval_alg q α hpl hpr]
  have :
    ∑ x ∈ rootsInInterval (toPolyReal α.p) ↑α.l ↑α.r, sgn (Polynomial.eval x (toPolyReal q)) =
    tarskiQuery (toPolyReal α.p) (toPolyReal q) α.l α.r := by simp [tarskiQuery]
  rw [this, cauchyIndex_poly_taq, <- cauchyIndex_sturmSeq]
  · rw [<- seqVarABEquivSturm α.p q α.l α.r]
    exact seqVarSturmC_ab_equiv α.p (α.p.derivative * q) α.l α.r
  · rw [CPolynomial.eval_toPoly, <- (Rat.cast_ne_zero (α := Real)), eval_comm_map] at hpl
    exact hpl
  · rw [CPolynomial.eval_toPoly, <- (Rat.cast_ne_zero (α := Real)), eval_comm_map] at hpr
    exact hpr
  · have := AlgNum.lr' α hpl
    exact Real.ratCast_lt.mpr this

open Qq Lean Elab Tactic Meta

syntax (name := compute_sign) "compute_sign" term "," term : tactic

lemma minus_one (a : Int) : a = -1 → a < 0 := by
  intro h
  simp_all only [Int.reduceNeg, Int.neg_neg_iff_pos, zero_lt_one]

lemma plus_one (a : Int) : a = 1 → a > 0 := by
  intro h
  positivity

lemma eval_neg (a : Rat) (p : CPolynomial Rat) (h_eval : p.eval a < 0) : (toPolyReal p).eval (ratToRealHom a) < 0 := by
  unfold toPolyReal
  rw [CPolynomial.eval_toPoly] at h_eval
  have : (↑(p.toPoly.eval a) : Real) < 0 := by simp_all only [Rat.cast_lt_zero]
  rw [eval_comm_map] at this
  unfold ratToRealHom at this ⊢
  finiteness

lemma eval_zero (a : Rat) (p : CPolynomial Rat) (h_eval : p.eval a = 0) : (toPolyReal p).eval (ratToRealHom a) = 0 := by
  unfold toPolyReal
  rw [CPolynomial.eval_toPoly] at h_eval
  have : (↑(p.toPoly.eval a) : Real) = 0 := by simp_all only [Rat.cast_zero]
  rw [eval_comm_map] at this
  unfold ratToRealHom at this ⊢
  finiteness

lemma eval_pos (a : Rat) (p : CPolynomial Rat) (h_eval : p.eval a > 0) : (toPolyReal p).eval (ratToRealHom a) > 0 := by
  unfold toPolyReal
  rw [CPolynomial.eval_toPoly] at h_eval
  have : (↑(p.toPoly.eval a) : Real) > 0 := by positivity
  rw [eval_comm_map] at this
  unfold ratToRealHom at this ⊢
  finiteness

def getSignProof (p : Q(CPolynomial Rat)) (a : Q(AlgNum)) : MetaM (Expr × Int) := do
  let ta ← inferType a
  if ta == .const ``Rat [] then
    let a : Q(Rat) := a
    let val : Int ← unsafe Meta.evalExpr Int q(Int) q(sgnC (CPolynomial.eval $a $p))
    let pf: Expr ← do
      if val < 0 then
        let goal := q(CPolynomial.eval $a $p < 0)
        let pf_rat ← mkDecideProof goal
        mkAppM ``eval_neg #[a, p, pf_rat]
      else if val = 0 then
        let goal := q(CPolynomial.eval $a $p = 0)
        let pf_rat ← mkDecideProof goal
        mkAppM ``eval_zero #[a, p, pf_rat]
      else
        let goal := q(CPolynomial.eval $a $p > 0)
        let pf_rat ← mkDecideProof goal
        mkAppM ``eval_pos #[a, p, pf_rat]
    return (pf, val)
  let h1 : Q(Prop) := q(«$a».p.eval «$a».l ≠ 0)
  let p1 : Q($h1) ← mkDecideProof h1
  let h2 : Q(Prop) := q(«$a».p.eval «$a».r ≠ 0)
  let p2 : Q($h2) ← mkDecideProof h2
  let sign_sturm_pf := q(sgn_eval_alg_sturm_seq $p $a $p1 $p2)
  let seqVar : Q(Int) := q(seqVarSturmC_ab' «$a».p («$a».p.derivative * $p) «$a».l «$a».r)
  let sign : Int ← unsafe Meta.evalExpr Int q(Int) seqVar
  let sign_eq : Q(Prop) := q(seqVarSturmC_ab' «$a».p («$a».p.derivative * $p) «$a».l «$a».r = $sign)
  let sign_reflection ← mkDecideProof sign_eq
  let sign_pf : Q(sgn ((toPolyReal $p).eval «$a».toReal) = $sign) ← mkAppM ``Eq.trans #[sign_sturm_pf, sign_reflection]
  if sign = -1 then
    let sign_neg_pf : Q(sgn ((toPolyReal $p).eval «$a».toReal) < 0) ← mkAppM ``minus_one #[q(sgn ((toPolyReal $p).eval «$a».toReal)), sign_pf]
    return (q((sgn_sgn_neg ((toPolyReal $p).eval «$a».toReal)).mp $sign_neg_pf), sign)
  else if sign = 0 then
    let sign_pf : Q(sgn ((toPolyReal $p).eval «$a».toReal) = 0) := sign_pf
    return (q((sgn_sgn_zero ((toPolyReal $p).eval «$a».toReal)).mp $sign_pf), sign)
  else
    let sign_pos_pf : Q(sgn ((toPolyReal $p).eval «$a».toReal) > 0) ← mkAppM ``plus_one #[q(sgn ((toPolyReal $p).eval «$a».toReal)), sign_pf]
    return (q((sgn_sgn_pos ((toPolyReal $p).eval «$a».toReal)).mp $sign_pos_pf), sign)

@[tactic compute_sign] def evalComputeSign : Tactic := fun stx => withMainContext do
  let p : Q(CPolynomial Rat) ← elabTerm stx[1] none
  let a : Q(AlgNum) ← elabTerm stx[3] none
  let v ← getSignProof p a
  closeMainGoal .anonymous v.1

namespace tests_sgn

open CPolynomial in
def P1 : CPolynomial Rat := X ^ 3 - 3 * X ^ 2 + X - 5

open CPolynomial in
def Q : CPolynomial Rat := X ^ 2 - 2
def r : Raw := ⟨Q, 1, 2⟩
def α : AlgNum := by lift_alg_num r -- sqrt(2)

example : (toPolyReal P1).eval α.toReal < 0 := by
  compute_sign P1 , α

open CPolynomial in
def P2 : CPolynomial Rat := X ^ 3 - 3 * X ^ 2 + X + 5

example : (toPolyReal P2).eval α.toReal > 0 := by
  compute_sign P2 , α

example : (toPolyReal Q).eval α.toReal = 0 := by
  compute_sign Q , α

def r1 : Rat := 27 / 3
example : (toPolyReal Q).eval (ratToRealHom r1) > 0 := by
  compute_sign Q , r1

def Pr : CPolynomial Rat := 2 * CPolynomial.X - 3
def r2 : Rat := 3 / 2

example : (toPolyReal Pr).eval (ratToRealHom r2) = 0 := by
  compute_sign Pr , r2

end tests_sgn
