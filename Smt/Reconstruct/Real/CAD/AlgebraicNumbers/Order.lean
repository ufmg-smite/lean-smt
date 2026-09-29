import Mathlib
import Lean.Elab.Tactic.Basic
import Qq

import CompPoly
import Smt.Reconstruct
import Smt.Reconstruct.Real.CAD.RootVal
import Smt.Reconstruct.Real.CAD.Utils
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.AlgNum
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.DeriveWellDefined

open Qq Lean Elab Tactic ToExpr Meta
open AlgebraicNumber
open CompPoly

lemma cmp_rat_alg_ra (a : Rat) (b : AlgNum) : a < b.l → ratToReal a < b.toReal := by
  intro h
  have h1 := (toReal_bounds b).1
  have h2 : ratToReal a < b.l := by unfold ratToReal; simp_all only [eq_ratCast, Rat.cast_lt]
  exact Std.lt_of_lt_of_le h2 h1

lemma cmp_rat_alg_refine_ra (a : Rat) (b : AlgNum) : ratToReal a < b.refine.toReal → ratToReal a < b.toReal := by
  intro h
  rw [refine_toReal]
  exact h

lemma cmp_rat_alg_ar (a : AlgNum) (b : Rat) : a.r < b → a.toReal < ratToReal b := by
  intro h
  have h1 := (toReal_bounds a).2
  have h2 : a.r < ratToReal b := by unfold ratToReal; simp_all only [eq_ratCast, Rat.cast_lt]
  exact Std.lt_of_le_of_lt h1 h2

lemma cmp_rat_alg_refine_ar (a : AlgNum) (b : Rat) : a.refine.toReal < ratToReal b → a.toReal < ratToReal b := by
  intro h
  rw [refine_toReal]
  exact h

lemma ratToReal_lt (a b : Rat) : a < b → ratToReal a < ratToReal b := by
  intro h
  unfold ratToReal
  simp_all only [eq_ratCast, Rat.cast_lt]

def gen_toReal_lt_rr (aE bE : Q(Rat)) : Smt.ReconstructM Expr := do
  let goal ← mkAppM `LT.lt #[aE,bE]
  let pf ← mkDecideProof' goal
  mkAppM ``ratToReal_lt #[aE, bE, pf]

/-- Maximal number of refinements tried before giving up on a comparison. Each refinement halves
the isolating interval, so this is never reached for a true strict comparison between numbers
whose bounds are not roots (as cvc5's are); it only guards against a false or degenerate input. -/
def maxRefinements : Nat := 256

/-- `ratToReal a < b.toReal`, for `b` algebraic. The isolating bound `b.l` need not exceed `a`
(cvc5 uses `b.l` itself as a window end), so a copy of `b` is refined until it does; the
statement keeps the original `b`, the transfer is `cmp_rat_alg_refine_ra`. -/
partial def gen_toReal_lt_ra (aE bE : Expr) (va : Rat) (vb : Raw) (fuel : Nat := maxRefinements) :
    Smt.ReconstructM Expr := do
  if va < vb.l then
    let goal ← mkAppM `LT.lt #[aE, ← mkAppM ``AlgNum.l #[bE]]
    let h ← mkDecideProof' goal
    mkAppM ``cmp_rat_alg_ra #[aE, bE, h]
  else
    if fuel == 0 then throwError "[gen_toReal_lt]: cannot separate {aE} from {bE}"
    let pf ← gen_toReal_lt_ra aE (mkApp (mkConst ``AlgNum.refine) bE) va vb.refine (fuel - 1)
    mkAppM ``cmp_rat_alg_refine_ra #[aE, bE, pf]

/-- `a.toReal < ratToReal b`, for `a` algebraic; see `gen_toReal_lt_ra`. -/
partial def gen_toReal_lt_ar (aE bE : Expr) (va : Raw) (vb : Rat) (fuel : Nat := maxRefinements) :
    Smt.ReconstructM Expr := do
  if va.r < vb then
    let goal ← mkAppM `LT.lt #[← mkAppM ``AlgNum.r #[aE], bE]
    let h ← mkDecideProof' goal
    mkAppM ``cmp_rat_alg_ar #[aE, bE, h]
  else
    if fuel == 0 then throwError "[gen_toReal_lt]: cannot separate {aE} from {bE}"
    let pf ← gen_toReal_lt_ar (mkApp (mkConst ``AlgNum.refine) aE) bE va.refine vb (fuel - 1)
    mkAppM ``cmp_rat_alg_refine_ar #[aE, bE, pf]

/-- `a.toReal < b.toReal`, both algebraic; both copies are refined together until `a.r < b.l`,
the transfer is `refine_lt_toReal`. -/
partial def gen_toReal_lt_aa (aE bE : Expr) (va vb : Raw) (fuel : Nat := maxRefinements) :
    Smt.ReconstructM Expr := do
  if va.r < vb.l then
    let goal ← mkAppM `LT.lt #[aE, bE]
    let h ← mkDecideProof' goal
    mkAppM ``AlgebraicNumber.lt_toReal #[aE, bE, h]
  else
    if fuel == 0 then throwError "[gen_toReal_lt]: cannot separate {aE} from {bE}"
    let pf ← gen_toReal_lt_aa (mkApp (mkConst ``AlgNum.refine) aE) (mkApp (mkConst ``AlgNum.refine) bE)
      va.refine vb.refine (fuel - 1)
    mkAppM ``refine_lt_toReal #[aE, bE, pf]

def gen_toReal_lt (a b : RootVal) : Smt.ReconstructM Expr := do
  match a, b with
  | .alg aE va, .alg bE vb => gen_toReal_lt_aa aE bE va vb
  | .rat aE _, .rat bE _ => gen_toReal_lt_rr aE bE
  | .rat aE va, .alg bE vb => gen_toReal_lt_ra aE bE va vb
  | .alg aE va, .rat bE vb => gen_toReal_lt_ar aE bE va vb

def toListExpr (α : Q(Type*)) (es : List Q($α)) : Q(List $α) :=
  match es with
  | [] => q(@List.nil $α)
  | hd :: tl =>
    let tl' : Q(List $α) := toListExpr α tl
    q($hd :: $tl')

def getPfs (as : List RootVal) : Smt.ReconstructM (List Expr) :=
  match as with
  | [] => return []
  | _ :: [] => return []
  | a1 :: a2 :: as => do
    let pf ← gen_toReal_lt a1 a2
    let pfs ← getPfs (a2 :: as)
    return pf :: pfs

partial def separateIntervals (rs : List RootVal) : Smt.ReconstructM (List RootVal) :=
  match rs with
  | [] => return []
  | [r] => return [r]
  | .rat e1 v1 :: .rat e2 v2 :: rs => do
    let (r1', r2') ← separate_rr e1 e2 v1 v2
    return r1' :: (← separateIntervals (r2' :: rs))
  | .rat e1 v1 :: .alg e2 v2 :: rs => do
    let (r1', r2') ← separate_ra e1 e2 v1 v2
    return r1' :: (← separateIntervals (r2' :: rs))
  | .alg e1 v1 :: .rat e2 v2 :: rs => do
    let (r1', r2') ← separate_ar e1 e2 v1 v2
    return r1' :: (← separateIntervals (r2' :: rs))
  | .alg e1 v1 :: .alg e2 v2 :: rs => do
    let (r1', r2') ← separate_aa e1 e2 v1 v2
    return r1' :: (← separateIntervals (r2' :: rs))
where
  separate_rr (e1 e2 : Expr) (v1 v2 : Rat) : MetaM (RootVal × RootVal) := return (.rat e1 v1, .rat e2 v2)
  separate_ra (e1 e2 : Expr) (v1 : Rat) (v2 : Raw) : MetaM (RootVal × RootVal) :=
    if v1 < v2.l then
      return (.rat e1 v1, .alg e2 v2)
    else
      separate_ra e1 (mkApp (mkConst ``AlgNum.refine) e2) v1 v2.refine
  separate_ar (e1 e2 : Expr) (v1 : Raw) (v2 : Rat) : MetaM (RootVal × RootVal) :=
    if v1.r < v2 then
      return (.alg e1 v1, .rat e2 v2)
    else
      separate_ar (mkApp (mkConst ``AlgNum.refine) e1) e2 v1.refine v2
  separate_aa (e1 e2 : Expr) (v1 v2 : Raw) : MetaM (RootVal × RootVal) := do
    if v1.r < v2.l then
      return (.alg e1 v1, .alg e2 v2)
    else
      separate_aa (mkApp (mkConst ``AlgNum.refine) e1) (mkApp (mkConst ``AlgNum.refine) e2) v1.refine v2.refine

/-- A proof of `List.SortedLT [a₁, …, aₙ]` from proofs of `a₁ < a₂`, …, `aₙ₋₁ < aₙ`, as returned
by `getPfs`. The adjacent proofs form a `List.IsChain (· < ·)`, which is sortedness for a
transitive relation (`List.IsChain.sortedLT`). The term is linear in `n`. (`grind`, used here
before, fails from nine elements on: it goes through `Pairwise`, i.e. all `n(n-1)/2` pairs.) -/
def mkSortedLTPf (as : List Q(Real)) (pfs : List Expr) : MetaM Expr := do
  let l : Q(List Real) := toListExpr q(Real) as
  let chain : Q(List.IsChain (fun x y : Real => x < y) $l) ← go as pfs
  return q(List.IsChain.sortedLT $chain)
where
  go : List Q(Real) → List Expr → MetaM Expr
    | [], [] => pure q(List.IsChain.nil (R := fun x y : Real => x < y))
    | [a], [] => pure q(List.IsChain.singleton (R := fun x y : Real => x < y) $a)
    | a :: b :: rest, pf :: pfs => do
      let tl : Q(List Real) := toListExpr q(Real) rest
      let h : Q(List.IsChain (fun x y : Real => x < y) ($b :: $tl)) ← go (b :: rest) pfs
      let pf : Q($a < $b) := pf
      pure q(List.IsChain.cons_cons $pf $h)
    | as, pfs => throwError "mkSortedLTPf: {as.length} elements but {pfs.length} proofs"

-- given a list of RootVal, refines the intervals of the algebraic numbers
-- and produces a proof that the resulting list is sorted. Also returns the
-- updated list.
def genPfSortedLT (as : List RootVal) : Smt.ReconstructM (Expr × List RootVal) := do
  let as_refined ← separateIntervals as
  let pfs ← getPfs as_refined -- each pair is sorted
  let as_refined' : List Q(Real) ← as_refined.mapM RootVal.toReal
  let pf ← mkSortedLTPf as_refined' pfs
  return (pf, as_refined)

