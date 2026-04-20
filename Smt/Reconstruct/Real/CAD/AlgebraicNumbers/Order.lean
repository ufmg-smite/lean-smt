import Mathlib
import Lean.Elab.Tactic.Basic
import Qq

import CompPoly
import Smt.Reconstruct.Real.CAD.RootVal
import Smt.Reconstruct.Real.CAD.Utils
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.AlgNum
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.DeriveWellDefined

open Qq Lean Elab Tactic ToExpr Meta
open AlgebraicNumber
open CompPoly

syntax (name := cmp_alg) "cmp_alg" term "," term : tactic

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

def gen_toReal_lt_rr (aE bE : Q(Rat)) : MetaM Expr := do
  let goal ← mkAppM `LT.lt #[aE,bE]
  let pf ← mkDecideProof goal
  mkAppM ``ratToReal_lt #[aE, bE, pf]

partial def gen_toReal_lt_ra (aE bE : Expr) (av : Rat) (bV : Raw) : MetaM Expr := do
  if av < bV.l then
    let goal ← mkAppM `LT.lt #[aE, ← mkAppM ``AlgNum.l #[bE]]
    let h ← mkDecideProof goal
    mkAppM ``cmp_rat_alg_ra #[aE, bE, h]
  else
    let bE' := mkApp (mkConst ``AlgNum.refine) bE
    let bV' := bV.refine
    let sub ← gen_toReal_lt_ra aE bE' av bV' -- ratToReal a < b.refine.toReal
    mkAppM ``cmp_rat_alg_refine_ra #[aE, bE, sub]

partial def gen_toReal_lt_ar (aE bE : Expr) (aV : Raw) (bv : Rat) : MetaM Expr := do
  let aE : Q(AlgNum) := aE
  if aV.r < bv then
    let goal ← mkAppM `LT.lt #[q(AlgNum.r $aE), bE]
    let h ← mkDecideProof goal
    mkAppM ``cmp_rat_alg_ar #[aE, bE, h]
  else
    let aE' := mkApp (mkConst ``AlgNum.refine) aE
    let aV' := aV.refine
    let sub ← gen_toReal_lt_ar aE' bE aV' bv
    mkAppM ``cmp_rat_alg_refine_ar #[aE, bE, sub]

partial def gen_toReal_lt_aa (aE bE : Expr) (aV bV : Raw) : MetaM Expr := do
  if aV.r < bV.l then
    let t3 ← IO.monoMsNow
    let goal ← mkAppM `LT.lt #[aE, bE]
    let h ← mkDecideProof goal
    let t4 ← IO.monoMsNow
    logInfo m!"deciding that a < b took {t4 - t3}ms"
    mkAppM ``AlgebraicNumber.lt_toReal #[aE, bE, h]
  else
    let aE' := mkApp (mkConst ``AlgNum.refine) aE
    let aV' := aV.refine
    let bE' := mkApp (mkConst ``AlgNum.refine) bE
    let bV' := bV.refine
    let sub ← gen_toReal_lt_aa aE' bE' aV' bV'
    mkAppM ``refine_lt_toReal #[aE, bE, sub]

partial def gen_toReal_lt (a b : RootVal) : MetaM Expr := do
  match a, b with
  | .alg aE aV, .alg bE bV => gen_toReal_lt_aa aE bE aV bV
  | .rat aE _, .rat bE _ => gen_toReal_lt_rr aE bE
  | .rat aE aV, .alg bE bV => gen_toReal_lt_ra aE bE aV bV
  | .alg aE aV, .rat bE bv => gen_toReal_lt_ar aE bE aV bv

@[tactic cmp_alg] def evalCmp_alg : Tactic := fun stx => withMainContext do
  let a ← elabTerm stx[1] none
  let b ← elabTerm stx[3] none
  let aE ← RootVal.ofExpr a
  let bE ← RootVal.ofExpr b
  let e ← gen_toReal_lt aE bE
  closeMainGoal .anonymous e

def a : Raw := ⟨CPolynomial.X, -500, 500⟩ -- 0
def b : Raw := ⟨CPolynomial.X ^ 2 - CPolynomial.C 2, 0, 2⟩ -- sqrt 2
def c : Raw := ⟨CPolynomial.X - CPolynomial.C 3, -500, 500⟩ -- 3
def d : Raw := ⟨CPolynomial.X - CPolynomial.C 10, -500, 500⟩ -- 10

def A : AlgNum := by lift_alg_num a
def A2 : Rat := 2 / 3
def B : AlgNum := by lift_alg_num b
def C : AlgNum := by lift_alg_num c
def C2 : Rat := 7 / 2
def D : AlgNum := by lift_alg_num d

example : A.toReal < B.toReal := by
  cmp_alg A , B

def toListExpr (α : Q(Type*)) (es : List Q($α)) : Q(List $α) :=
  match es with
  | [] => q(@List.nil $α)
  | hd :: tl =>
    let tl' : Q(List $α) := toListExpr α tl
    q($hd :: $tl')

def getPfs (as : List RootVal) : MetaM (List Expr) :=
  match as with
  | [] => return []
  | _ :: [] => return []
  | a1 :: a2 :: as => do
    let p ← gen_toReal_lt a1 a2
    let rest ← getPfs (a2 :: as)
    return p :: rest

-- given a list of algebraic numbers and a list of proofs that they are well
-- defined, tries to create a proof that the list is sorted (`List.SortedLT`)
def genPfSortedLT (as : List RootVal) : MetaM Expr := do
  let pfs ← getPfs as -- each pair is sorted
  let as' : List Q(Real) ← as.mapM RootVal.toReal
  let as := toListExpr q(Real) as'
  let goal ← mkAppM `List.SortedLT #[as]
  let mv ← mkFreshExprMVar goal
  let t1 ← IO.monoMsNow
  let ok ← runGrind' mv.mvarId! pfs
  if !ok then throwError "grind failed 9"
  let t2 ← IO.monoMsNow
  logInfo m!"proving list is SortedLT took {t2 - t1}ms"
  return mv

syntax (name := cmp_alg_list) "cmp_alg_list" ("[" term,* "]") : tactic

def parse_cmp_alg_list : Syntax → TacticM (List Expr)
  | `(tactic| cmp_alg_list [ $[$as],* ] ) => as.toList.mapM (elabTerm · none)
  | _ => throwError "[parse_cmp_alg_list]: impossible"

@[tactic cmp_alg_list] def evalCmp_alg_list : Tactic := fun stx => withMainContext do
  let as ← parse_cmp_alg_list stx
  let rvs ← as.mapM (fun e => RootVal.ofExpr e)
  let e ← genPfSortedLT rvs
  closeMainGoal .anonymous e

namespace order_tests

lemma l1 : [A.toReal, ratToReal A2, B.toReal, C.toReal, ratToReal C2, D.toReal].SortedLT := by
  cmp_alg_list [A, A2, B, C, C2, D]

#print axioms l1

lemma l2 : [ratToReal A2, ratToReal C2].SortedLT := by
  cmp_alg_list [A2, C2]

#print axioms l2

end order_tests
