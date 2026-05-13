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

partial def gen_toReal_lt_ra (aE bE : Expr) : Smt.ReconstructM Expr := do
  let goal ← mkAppM `LT.lt #[aE, ← mkAppM ``AlgNum.l #[bE]]
  let h ← mkDecideProof' goal
  mkAppM ``cmp_rat_alg_ra #[aE, bE, h]

partial def gen_toReal_lt_ar (aE bE : Expr) : Smt.ReconstructM Expr := do
  let goal ← mkAppM `LT.lt #[← mkAppM ``AlgNum.r #[aE], bE]
  let h ← mkDecideProof' goal
  mkAppM ``cmp_rat_alg_ar #[aE, bE, h]

partial def gen_toReal_lt_aa (aE bE : Expr) : Smt.ReconstructM Expr := do
  let goal ← mkAppM `LT.lt #[aE, bE]
  let h ← mkDecideProof' goal
  let pf ← mkAppM ``AlgebraicNumber.lt_toReal #[aE, bE, h]
  return pf

partial def gen_toReal_lt (a b : RootVal) : Smt.ReconstructM Expr := do
  match a, b with
  | .alg aE _, .alg bE _ => gen_toReal_lt_aa aE bE
  | .rat aE _, .rat bE _ => gen_toReal_lt_rr aE bE
  | .rat aE _, .alg bE _ => gen_toReal_lt_ra aE bE
  | .alg aE _, .rat bE _ => gen_toReal_lt_ar aE bE

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
  separate_aa (e1 e2 : Expr) (v1 v2 : Raw) : MetaM (RootVal × RootVal) :=
    if v1.r < v2.l then
      return (.alg e1 v1, .alg e2 v2)
    else
      separate_aa (mkApp (mkConst ``AlgNum.refine) e1) (mkApp (mkConst ``AlgNum.refine) e2) v1.refine v2.refine

-- given a list of RootVal, refines the intervals of the algebraic numbers
-- and produces a proof that the resulting list is sorted. Also returns the
-- updated list.
def genPfSortedLT (as : List RootVal) : Smt.ReconstructM (Expr × List RootVal) := do
  let as_refined ← separateIntervals as
  let pfs ← getPfs as_refined -- each pair is sorted
  let as_refined' : List Q(Real) ← as_refined.mapM RootVal.toReal
  let as_refined'' := toListExpr q(Real) as_refined'
  let goal ← mkAppM `List.SortedLT #[as_refined'']
  let mv ← mkFreshExprMVar goal
  let t1 ← IO.monoMsNow
  let ok ← runGrind' mv.mvarId! pfs
  if !ok then throwError "grind failed 9"
  let t2 ← IO.monoMsNow
  logInfo m!"proving list is SortedLT took {t2 - t1}ms"
  return (mv, as_refined)

syntax (name := cmp_alg_list) "cmp_alg_list" ("[" term,* "]") : tactic

def parse_cmp_alg_list : Syntax → TacticM (List Expr)
  | `(tactic| cmp_alg_list [ $[$as],* ] ) => as.toList.mapM (elabTerm · none)
  | _ => throwError "[parse_cmp_alg_list]: impossible"

@[tactic cmp_alg_list] def evalCmp_alg_list : Tactic := fun stx => withMainContext do
  let as ← parse_cmp_alg_list stx
  let rvs ← as.mapM (fun e => RootVal.ofExpr e)
  let (e, rvs') ← ((genPfSortedLT rvs).run {}).run' {}
  logInfo m!"refined root list: {rvs'}"
  logInfo m!"got proof of: {← inferType e}"
