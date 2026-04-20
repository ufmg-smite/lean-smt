import Lean
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.AlgNum
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.DeriveWellDefined

open Lean Qq

open AlgebraicNumber CompPoly CPolynomial

inductive RootVal where
  | rat (e : Expr) (v : Rat) : RootVal
  -- NOTE: They do NOT represent the same thing; the Expr is an `AlgNum`
  -- and raw is the underlying `Raw`. Unfortunately we can't generate
  -- the `AlgNum` at compile time, so we can't store it here. But it
  -- is very convenient to have the `Expr` stored as the full `AlgNum`.
  | alg (e : Q(AlgNum)) (raw : Raw) : RootVal
  deriving Inhabited

def RootVal.expr : RootVal → Expr
  | .rat e _ => e
  | .alg e _ => e

def RootVal.isAlgNum : RootVal → Bool
  | .rat .. => false
  | .alg .. => true

def RootVal.ofExpr (e : Expr) : MetaM RootVal := do
  let t ← Meta.inferType e
  if t == .const ``Rat [] then
    let v : Rat ← unsafe Meta.evalExpr Rat q(Rat) e
    return .rat e v
  else if t == .const ``AlgNum [] then
    let e : Q(AlgNum) := e
    let p : CPolynomial Rat ← unsafe Meta.evalExpr (CPolynomial Rat) q(CPolynomial Rat) q(AlgNum.p $e)
    let l : Rat ← unsafe Meta.evalExpr Rat q(Rat) q(AlgNum.l $e)
    let r : Rat ← unsafe Meta.evalExpr Rat q(Rat) q(AlgNum.r $e)
    let raw: Raw := ⟨p, l, r⟩
    return .alg e raw
  else
    throwError "[RootVal.ofExpr]: expected Rat or AlgNum, got {t}"

def RootVal.toReal : RootVal → MetaM Expr
  | .rat e _ => let q : Q(Rat) := e; return q(ratToReal $q)
  | .alg e _ => Meta.mkAppM ``AlgNum.toReal #[e]
