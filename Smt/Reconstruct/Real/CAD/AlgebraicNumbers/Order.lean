import Mathlib
import Lean.Elab.Tactic.Basic
import Qq

import CompPoly
import Smt.Reconstruct.Real.CAD.Utils
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.AlgNum
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.DeriveWellDefined

open Qq Lean Elab Tactic ToExpr Meta
open AlgebraicNumber
open CompPoly

syntax (name := cmp_alg) "cmp_alg" term "," term : tactic

partial def gen_toReal_lt (a b : Q(AlgNum)) : MetaM Expr := do
  let goal ← mkAppM `LT.lt #[a, b]
  let ar : Rat ← unsafe evalExpr Rat q(Rat) q(AlgNum.r $a)
  let bl : Rat ← unsafe evalExpr Rat q(Rat) q(AlgNum.l $b)
  if ar < bl then
    let h ← mkDecideProof goal
    mkAppM ``AlgebraicNumber.lt_toReal #[a,b,h]
  else
    let a' := mkApp (.const ``AlgNum.refine []) a
    let b' := mkApp (.const ``AlgNum.refine []) b
    let sub ← gen_toReal_lt a' b'
    mkAppM ``refine_lt_toReal #[a,b,sub]

@[tactic cmp_alg] def evalCmp_alg : Tactic := fun stx => withMainContext do
  let a : Q(AlgNum) ← elabTerm stx[1] none
  let b : Q(AlgNum) ← elabTerm stx[3] none
  let e ← gen_toReal_lt a b
  closeMainGoal .anonymous e

def a : Raw := ⟨CPolynomial.X, -500, 500⟩ -- 0
def b : Raw := ⟨CPolynomial.X ^ 2 - CPolynomial.C 2, 0, 2⟩ -- sqrt 2
def c : Raw := ⟨CPolynomial.X - CPolynomial.C 3, -500, 500⟩ -- 3
def d : Raw := ⟨CPolynomial.X - CPolynomial.C 10, -500, 500⟩ -- 10

def A : AlgNum := by lift_alg_num a
def B : AlgNum := by lift_alg_num b
def C : AlgNum := by lift_alg_num c
def D : AlgNum := by lift_alg_num d

example : A.toReal < B.toReal := by
  cmp_alg A , B

def toListExpr (α : Q(Type*)) (es : List Q($α)) : Q(List $α) :=
  match es with
  | [] => q(@List.nil $α)
  | hd :: tl =>
    let tl' : Q(List $α) := toListExpr α tl
    q($hd :: $tl')

def getPfs (as : List Expr) : MetaM (List Expr) :=
  match as with
  | [] => return []
  | _ :: [] => return []
  | a1 :: a2 :: as => do
    let p ← gen_toReal_lt a1 a2
    let rest ← getPfs (a2 :: as)
    return p :: rest

-- given a list of algebraic numbers and a list of proofs that they are well
-- defined, tries to create a proof that the list is sorted (`List.SortedLT`)
def genPfSortedLT (as : List Q(AlgNum)) : MetaM Expr := do
  let pfs ← getPfs as -- each pair is sorted
  let as' ← as.mapM (fun a => mkAppM ``AlgNum.toReal #[a])
  let as := toListExpr q(Real) as'
  let goal ← mkAppM `List.SortedLT #[as]
  let mv ← mkFreshExprMVar goal
  runGrind' mv.mvarId! pfs
  return mv

syntax (name := cmp_alg_list) "cmp_alg_list" ("[" term,* "]") : tactic

def parse_cmp_alg_list : Syntax → TacticM (List Expr)
  | `(tactic| cmp_alg_list [ $[$as],* ] ) => as.toList.mapM (elabTerm · none)
  | _ => throwError "[parse_cmp_alg_list]: impossible"

@[tactic cmp_alg_list] def evalCmp_alg_list : Tactic := fun stx => withMainContext do
  let as ← parse_cmp_alg_list stx
  let e ← genPfSortedLT as
  closeMainGoal .anonymous e

example : [A.toReal, B.toReal, C.toReal, D.toReal].SortedLT := by
  cmp_alg_list [A, B, C, D]
