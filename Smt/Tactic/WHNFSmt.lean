import Smt.Tactic.WHNFConfigurable
import Lean.Elab.Term
import Lean.Elab.Binders

namespace Smt

open Lean

/-- Constants which SMT knows about and we thus don't want to unfold. -/
def opaqueConsts : Std.HashSet Name :=
  List.foldr (fun c s => s.insert c) Std.HashSet.empty
  [
    `Eq.eq,
    `BEq.beq,
    `bne,
    `true,
    `false,
    `And.and,
    `Or.or,
    `Not.not,
    `ite,
    `dite,
    `Exists.exists,
    `Add.add,
    `Sub.sub,
    `Mul.mul,
    `Div.div,
    `Mod.mod,
    `LE.le,
    `LT.lt,
    `GE.ge,
    `GT.gt,
    `and,
    `Xor.xor,
    `Nat.add,
    `HMod.hMod,
    `Not,
    `HAdd.hAdd,
    `HXor.hXor,
    `HShiftLeft.hShiftLeft,
    `HShiftRight.hShiftRight,
    `HPow.hPow,
    `HAppend.hAppend,
    `HSub.hSub,
    `BitVec,
    `BitVec.zero,
    `BitVec.ofNat,
    `BitVec.extract
  ]

def opaquePred (_ : Meta.Config) (ci : ConstantInfo) : CoreM Bool := do
  if opaqueConsts.contains ci.name then return false
  return true

/-- Runs type-theoretic reduction, but never unfolding SMT builtins and with extra rules
to produce linearly-sized terms from code containing `let_opaque` bindings. -/
def smtOpaqueReduce (e : Expr) : MetaM Expr :=
  withTheReader Meta.Context (fun ctx => { ctx with
    canUnfold? := some opaquePred
  }) do Smt.reduce (skipTypes := false) e |>.run {
    letPushElim := true
  }
  
open Parser in
syntax (name := «let_opaque») withPosition("let_opaque " letDecl) optional(";") term : term

open Elab Term in
/-- A `let_opaque` declaration is not eliminated via substitution during WHNFConfigurable normalization,
but rather persists in the output term. -/
@[termElab «let_opaque»] def elabLetOpaqueDecl : TermElab := fun stx expectedType? => do
  let e ← elabLetDeclCore stx expectedType? (useLetExpr := true) (elabBodyFirst := false) (usedLetOnly := false)
  return mkMData ({ : MData}.insert `zeta false) e

open Lean.Parser.Term
syntax "let_opaque " letDecl : doElem
syntax "opaque" doReassign : doElem

macro_rules
  | `(doElem| let_opaque $id:ident := $t:term) => do
    `(doElem| let $id := (let_opaque v := $t; v))
  | `(doElem| opaque $id:ident := $t:term) => do
    `(doElem| $id:ident := (let_opaque v := $t; v))

end Smt
