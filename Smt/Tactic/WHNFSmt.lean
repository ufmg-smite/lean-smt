/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
import Smt.Tactic.WHNFConfigurable
import Lean.Elab.Term
import Lean.Elab.Binders

namespace Smt

open Lean

/-- Constants which SMT knows about and we thus don't want to unfold. -/
def smtConsts : Std.HashSet Name :=
  List.foldr (fun c s => s.insert c) Std.HashSet.empty
  [
    ``Eq,
    ``BEq.beq,
    ``bne,
    ``true,
    ``false,
    ``And,
    ``Or,
    ``Not,
    ``ite,
    ``dite,
    ``Exists,
    ``HAdd.hAdd,
    ``HSub.hSub,
    ``HMul.hMul,
    ``HDiv.hDiv,
    ``HMod.hMod,
    ``HPow.hPow,
    ``HAppend.hAppend,
    ``HAnd.hAnd,
    ``HXor.hXor,
    ``HOr.hOr,
    ``HShiftLeft.hShiftLeft,
    ``HShiftRight.hShiftRight,
    ``LE.le,
    ``LT.lt,
    ``GE.ge,
    ``GT.gt,
    ``and,
    ``or,
    ``not,
    `BitVec,
    `BitVec.zero,
    `BitVec.ofNat,
    `BitVec.extract,
    /- Eager WHNF unfolds implicit arguments in a way that interacts badly with the projection
    unfolding in `smt`. For example, `@Xor.xor (BitVec n) (instXorBitVec n)` goes to
    `@Xor.xor (BitVec n) { val := ... : Fin (2^n) }` and then we get `{ .. : Fin (2^n) }`
    as the instance. To make projection unfolding work, we prefer `@Xor.xor (BitVec n) BitVec.xor`,
    so the extra symbols are blocked here. This is not great, so maybe:
    - investigate using `explicitOnly` in `whnfCore`?
    - stop unfolding projections in `smt`?
    - something else? -/
    `BitVec.append,
    `BitVec.and,
    `BitVec.or,
    `BitVec.xor,
    `BitVec.shiftLeft,
    `BitVec.shiftRight,
    ``Nat.add,
    ``Nat.mul,
    ``Nat.div,
    ``Nat.mod,
    ``UInt16.ofNat,
    ``UInt16.add,
    ``UInt16.sub,
    ``UInt16.mul,
    ``UInt16.div,
    ``UInt16.mod,
    ``UInt16.modn,
    ``UInt16.land,
    ``UInt16.lor,
    ``UInt16.xor,
    ``UInt16.shiftLeft,
    ``UInt16.shiftRight,
    ``UInt32.ofNat,
    ``UInt32.add,
    ``UInt32.sub,
    ``UInt32.mul,
    ``UInt32.div,
    ``UInt32.mod,
    ``UInt32.modn,
    ``UInt32.land,
    ``UInt32.lor,
    ``UInt32.xor,
    ``UInt32.shiftLeft,
    ``UInt32.shiftRight
  ]

def opaquePred (opaqueConsts : Std.HashSet Name) (_ : Meta.Config) (ci : ConstantInfo) : CoreM Bool := do
  if smtConsts.contains ci.name || opaqueConsts.contains ci.name then
    return false
  return true

/-- Runs type-theoretic reduction, but never unfolding SMT builtins and with extra rules
to let-lift `let-opaque` bindings. This can produce linearly-sized terms in certain cases. 

Constants with names in `opaqueConsts` are also not unfolded. -/
def smtOpaqueReduce (e : Expr) (opaqueConsts : Std.HashSet Name := {}) : MetaM Expr :=
  withTheReader Meta.Context (fun ctx => { ctx with
    canUnfold? := some (opaquePred opaqueConsts)
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
/-- A `let_opaque` declaration is not eliminated via substitution during WHNFConfigurable normalization,
but rather persists in the output term. -/
syntax "let_opaque " letDecl : doElem
/-- An `opaque` reassignment is not eliminated via substitution during WHNFConfigurable normalization,
but rather persists in the output term. -/
syntax "opaque" doReassign : doElem

macro_rules
  | `(doElem| let_opaque $id:ident := $t:term) => `(doElem| let $id := (let_opaque v := $t; v))
  | `(doElem| opaque $id:ident := $t:term) => `(doElem| $id:ident := (let_opaque v := $t; v))

end Smt
