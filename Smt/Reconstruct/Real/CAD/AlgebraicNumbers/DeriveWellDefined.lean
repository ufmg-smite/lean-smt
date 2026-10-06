import Lean
import Mathlib
import CompPoly
import Smt.Reconstruct
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.AlgNum
import Smt.Reconstruct.Real.CAD.Sturm.Decidable
import Smt.Reconstruct.Real.CAD.Sturm.Certificate

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
  have h0 : a.p.toPoly.map ratToRealHom ≠ 0 := Polynomial.map_ne_zero (toPoly_ne0_of_poly_ne0 a.p hp)
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

def Raw.lift (r : Q(Raw)) : Smt.ReconstructM Q(AlgNum) := do
  let g1 : Q(Prop) := q(Raw.p $r ≠ 0)
  let pf1 : Q($g1) ← mkDecideProof' g1
  let g2 : Q(Prop) := q((Raw.p $r).eval (Raw.l $r) ≠ 0)
  let pf2 : Q($g2) ← mkDecideProof' g2
  let g3 : Q(Prop) := q((Raw.p $r).eval (Raw.r $r) ≠ 0)
  let pf3 : Q($g3) ← mkDecideProof' g3
  let g4 : Q(Prop) := q((Raw.l $r) < (Raw.r $r))
  let pf4 : Q($g4) ← mkDecideProof' g4
  let g5 : Q(Prop) := q(Raw.sgnDiff $r)
  let pf5 : Q($g5) ← mkDecideProof' g5
  let g6 : Q(Prop) := q(seqVarSturmC_ab' (Raw.p $r) (Raw.p $r).derivative (Raw.l $r) (Raw.r $r) = 1)
  let pf6 : Q($g6) ← mkDecideProof' g6
  return q(AlgNum.mk $r $pf1 $pf2 $pf3 $pf4 $pf5 $pf6)

/-! ### Lifting with the Sturm sequence shipped by cvc5

cvc5 states an irrational algebraic number together with the Sturm sequence of its defining
polynomial, computed by pseudo-division over `ℤ`, with the pseudo-quotients. Instead of computing the
sequence in the kernel, `Raw.liftCert` checks the shipped one (`SturmCert.certOk`) and counts the
roots in the isolating interval on it. The constant factors relating it to the exact sequence are
computed here (`mkCertData`), not shipped. -/

/-- A polynomial of a shipped Sturm sequence, `(+ (+ 0 (* c₀ 1)) (* c₁ (* 1 x))) …`, over its only
variable. -/
partial def sturmPolyOfTerm (t : cvc5.Term) : Except String (CPolynomial ℚ) :=
  match t.getKind with
  | .CONST_RATIONAL => return CPolynomial.C t.getRationalValue!
  | .CONST_INTEGER => return CPolynomial.C t.getIntegerValue!
  | .ADD => t.getChildren.foldlM (fun acc c => return acc + (← sturmPolyOfTerm c)) 0
  | .SUB => do
    let cs := t.getChildren
    cs[1:].foldlM (fun acc c => return acc - (← sturmPolyOfTerm c)) (← sturmPolyOfTerm cs[0]!)
  | .NEG => return -(← sturmPolyOfTerm t[0]!)
  | .MULT => t.getChildren.foldlM (fun acc c => return acc * (← sturmPolyOfTerm c)) 1
  | k =>
    if t.getNumChildren == 0 then return CPolynomial.X
    else throw s!"unexpected {k} in the polynomial {t}"

/-- The expression of a list of expressions of type `ty`. -/
def mkListExpr (ty : Expr) : List Expr → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) ty
  | e :: es => mkApp3 (mkConst ``List.cons [Level.zero]) ty e (mkListExpr ty es)

/-- The expression of a polynomial of a shipped Sturm sequence, as the literal array of its
coefficients (`SturmCert.ofCoeffs`). -/
def polyExpr (p : CPolynomial ℚ) : Q(CPolynomial ℚ) :=
  let cs : List Q(ℚ) := (List.range (p.natDegree + 1)).map fun i => toExpr (p.coeff i)
  let csE : Q(List ℚ) := mkListExpr q(ℚ) cs
  q(SturmCert.ofCoeffs (List.toArray $csE))

/-- The arguments of `SturmCert.certOk` for a shipped sequence of `(quotient, polynomial)` pairs. -/
structure CertData where
  c0 : ℚ
  c1 : ℚ
  S0 : CPolynomial ℚ
  S1 : CPolynomial ℚ
  S : List (CPolynomial ℚ)
  steps : List (CPolynomial ℚ × ℚ × ℚ)
  fin : CPolynomial ℚ × ℚ

/-- Computes the constants of the certificate for the Sturm sequence of `(p, q)`: the factors `c0`,
`c1` of the first two elements, and for each further element `c` with quotient `q'` after `a`, `b`
the `m`, `k` with `m • a = q' * b - k • c` (`m` from the leading coefficients, `k` from the
remainder). The last remainder is checked zero with the exact quotient. -/
def mkCertData (p q : CPolynomial ℚ) (seq : List (CPolynomial ℚ × CPolynomial ℚ)) :
    Except String CertData := do
  -- a zero remainder at the end is not part of the sequence
  let seq := (seq.reverse.dropWhile (·.2 == 0)).reverse
  let polys := seq.toArray.map (·.2)
  let quots := seq.toArray.map (·.1)
  if polys.size < 2 then throw "a Sturm sequence needs at least two elements"
  if p == 0 || q == 0 then throw "zero polynomial"
  let S0 := polys[0]!
  let S1 := polys[1]!
  let mut steps : Array (CPolynomial ℚ × ℚ × ℚ) := #[]
  for i in [2:polys.size] do
    let a := polys[i-2]!
    let b := polys[i-1]!
    let c := polys[i]!
    let qi := quots[i]!
    if c == 0 then throw "zero element in a Sturm sequence"
    let m : ℚ := if qi == 0 then 1 else qi.leadingCoeff * b.leadingCoeff / a.leadingCoeff
    let R := CPolynomial.C m * a - qi * b
    let k := -R.leadingCoeff / c.leadingCoeff
    steps := steps.push (qi, m, k)
  let n := polys.size
  return { c0 := S0.leadingCoeff / p.leadingCoeff, c1 := S1.leadingCoeff / q.leadingCoeff,
           S0, S1, S := (polys.extract 2 n).toList, steps := steps.toList,
           fin := (polys[n-2]! / polys[n-1]!, 1) }

/-- The checks of `AlgNum.mk` other than the root count. -/
def Raw.liftChecks (r : Q(Raw)) : Smt.ReconstructM (Expr × Expr × Expr × Expr × Expr) := do
  let pf1 ← mkDecideProof' q(Raw.p $r ≠ 0)
  let pf2 ← mkDecideProof' q((Raw.p $r).eval (Raw.l $r) ≠ 0)
  let pf3 ← mkDecideProof' q((Raw.p $r).eval (Raw.r $r) ≠ 0)
  let pf4 ← mkDecideProof' q((Raw.l $r) < (Raw.r $r))
  let pf5 ← mkDecideProof' q(Raw.sgnDiff $r)
  return (pf1, pf2, pf3, pf4, pf5)

/-- The `(quotient, polynomial)` pairs of a shipped Sturm sequence, each an s-expression `(a b)`. -/
def sturmSeqOfTerms (ts : Array cvc5.Term) : Except String (List (CPolynomial ℚ × CPolynomial ℚ)) :=
  ts.toList.mapM fun e => do
    if e.getNumChildren != 2 then throw s!"expected a pair (quotient polynomial), got {e}"
    return (← sturmPolyOfTerm e[0]!, ← sturmPolyOfTerm e[1]!)

/-- A checked certificate for the Sturm sequence of `(p, p')`: its data, the expression of the
sequence `S0 :: S1 :: S`, and a proof of `SturmCert.certOk p p.derivative … = true`. -/
structure SturmCertProof where
  data : CertData
  seq : Expr
  proof : Expr

/-- The sequence of a certificate, natively. -/
def CertData.seq (d : CertData) : List (CPolynomial ℚ) := d.S0 :: d.S1 :: d.S

/-- Checks the shipped Sturm sequence `seq` of `(p, q)` natively, then builds the kernel proof of
the certificate; `pE`, `qE` are the expressions of `p`, `q`. -/
def mkSturmCertFor (pE qE : Q(CPolynomial ℚ)) (p q : CPolynomial ℚ)
    (seq : List (CPolynomial ℚ × CPolynomial ℚ)) : Smt.ReconstructM SturmCertProof := do
  let d ← match mkCertData p q seq with
    | .ok d => pure d
    | .error e => throwError "[mkSturmCert]: {e}"
  unless SturmCert.certOk p q d.c0 d.c1 d.S0 d.S1 d.S d.steps d.fin do
    throwError "[mkSturmCert]: the shipped Sturm sequence does not check"
  let c0 : ℚ := d.c0
  let c1 : ℚ := d.c1
  let c0E : Q(ℚ) := q($c0)
  let c1E : Q(ℚ) := q($c1)
  let S0 := polyExpr d.S0
  let S1 := polyExpr d.S1
  let S := mkListExpr q(CPolynomial ℚ) (d.S.map polyExpr)
  let steps := mkListExpr q(CPolynomial ℚ × ℚ × ℚ)
    (d.steps.map fun (qi, m, k) => let qE := polyExpr qi; q(($qE, $m, $k)))
  let fin : Q(CPolynomial ℚ × ℚ) := let (qf, mf) := d.fin; let qE := polyExpr qf; q(($qE, $mf))
  let cert ← mkAppM ``SturmCert.certOk #[pE, qE, c0E, c1E, S0, S1, S, steps, fin]
  let hcert ← mkDecideProof' (← mkEq cert (mkConst ``Bool.true))
  let all := mkApp3 (mkConst ``List.cons [Level.zero]) q(CPolynomial ℚ) S0
    (mkApp3 (mkConst ``List.cons [Level.zero]) q(CPolynomial ℚ) S1 S)
  return { data := d, seq := all, proof := hcert }

/-- `mkSturmCertFor` for the Sturm sequence of `(p, p')`. -/
def mkSturmCert (pE : Q(CPolynomial ℚ)) (p : CPolynomial ℚ)
    (seq : List (CPolynomial ℚ × CPolynomial ℚ)) : Smt.ReconstructM SturmCertProof := do
  mkSturmCertFor pE (← mkAppM ``CPolynomial.derivative #[pE]) p p.derivative seq

/-- Proves `count = n` by `decide`, after checking it natively (`native`), so that a wrong count is
reported here rather than as a failed kernel reduction. -/
def decideCount (count : Expr) (native n : ℤ) : Smt.ReconstructM Expr := do
  unless native == n do
    throwError "[decideCount]: the shipped Sturm sequence counts {native}, expected {n}"
  let nE : Q(ℤ) := q($n)
  mkDecideProof' (← mkEq count nE)

/-- Like `Raw.lift`, with the root count taken from the shipped Sturm sequence `seq` of
`(quotient, polynomial)` pairs. `raw` is the native value of `r`. -/
def Raw.liftCert (r : Q(Raw)) (raw : Raw) (seq : List (CPolynomial ℚ × CPolynomial ℚ)) :
    Smt.ReconstructM Q(AlgNum) := do
  let c ← mkSturmCert q(Raw.p $r) raw.p seq
  unless seqVarQ_ab' c.data.seq raw.l raw.r == 1 do
    throwError "[Raw.liftCert]: the Sturm sequence does not count one root in the interval of {raw}"
  let (pf1, pf2, pf3, pf4, pf5) ← Raw.liftChecks r
  let lE : Q(ℚ) := q(Raw.l $r)
  let rE : Q(ℚ) := q(Raw.r $r)
  let count ← mkAppM ``seqVarQ_ab' #[c.seq, lE, rE]
  let hcount ← mkDecideProof' (← mkEq count q((1 : ℤ)))
  let pf6 ← mkEqTrans (← mkAppM ``SturmCert.seqVarSturmC_ab'_eq_of_certOk #[c.proof, lE, rE]) hcount
  return mkAppN (mkConst ``AlgNum.mk) #[r, pf1, pf2, pf3, pf4, pf5, pf6]

@[tactic lift_alg_num] def evalLiftAlgNum : Tactic := fun stx => withMainContext do
  let r: Q(Raw) ← elabTerm stx[1] none
  let a: Q(AlgNum) ← ((Raw.lift r).run {}).run' {}
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

end tests
