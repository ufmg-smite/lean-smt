/-
Copyright (c) 2021-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Qq
import Smt.Reconstruct.Builtin.Absorb
import Lean

namespace Smt.Reconstruct.Builtin

open Lean Qq

abbrev AbsorbM := StateT (Array Expr) MetaM

def getExprIndex (e : Expr) : AbsorbM Nat := do
  let es ← get
  if let some i := es.findIdx? (· == e) then
    return i
  else
    let size := es.size
    set (es.push e)
    return size

def reify (zero op e : Expr) : AbsorbM Q(Absorb.Expr) := do
  if e == zero then
    return .const ``Absorb.Expr.zero []
  if let .app (.app f l) r := e then if f == op then
    let l ← reify zero op l
    let r ← reify zero op r
    return mkApp2 (.const ``Absorb.Expr.op []) l r
  let i ← getExprIndex e
  return .app (.const ``Absorb.Expr.atom []) (mkNatLit i)

def absorb (mv : MVarId) (zero op : Expr) : MetaM Unit := do
  let some (α, l, _) := (← mv.getType).eq?
    | throwError "[absorb] expected an equality, got {← mv.getType}"
  let u ← Meta.getDecLevel α
  let α : Q(Type $u) ← pure α
  let op : Q($α → $α → $α) ← pure op
  let hα : Q(Absorb $op) ← Meta.synthInstance q(Absorb $op)
  let (l, es) ← (reify zero op l).run #[]
  let es : Q(Array $α) ← pure (es.foldl (fun acc (e : Q($α)) => q(«$acc».push $e)) q(#[]))
  let ctx : Q(Absorb.Context $α) := q((«$es».getD · «$hα».zero))
  let h : Q(«$l».containsZero) := .app q(@Eq.refl.{1} Bool) q(true)
  mv.assign q(@Absorb.Expr.eval_eq_zero_from_containsZero $α $op $l $hα $ctx $h)

def nativeAbsorb (mv : MVarId) (zero op : Expr) : MetaM Unit := do
  let some (α, l, _) := (← mv.getType).eq?
    | throwError "[absorb] expected an equality, got {← mv.getType}"
  let u ← Meta.getDecLevel α
  let α : Q(Type $u) ← pure α
  let op : Q($α → $α → $α) ← pure op
  let hα : Q(Absorb $op) ← Meta.synthInstance q(Absorb $op)
  let (l, es) ← (reify zero op l).run #[]
  let es : Q(Array $α) ← pure (es.foldl (fun acc (e : Q($α)) => q(«$acc».push $e)) q(#[]))
  let ctx : Q(Absorb.Context $α) := q((«$es».getD · «$hα».zero))
  let h ← nativeDecide q(«$l».containsZero)
  mv.assign q(@Absorb.Expr.eval_eq_zero_from_containsZero $α $op $l $hα $ctx $h)
where
  nativeDecide (p : Q(Prop)) : MetaM Q($p) := do
    let hp : Q(Decidable $p) ← Meta.synthInstance q(Decidable $p)
    let auxDeclName ← mkNativeAuxDecl `_nativePolynorm q(Bool) q(decide $p)
    let b : Q(Bool) := .const auxDeclName []
    return .app q(@of_decide_eq_true $p $hp) (.app q(Lean.ofReduceBool $b true) q(Eq.refl true))
  mkNativeAuxDecl (baseName : Name) (type value : Expr) : MetaM Name := do
    let auxName ← match (← getEnv).asyncPrefix? with
      | none          => Lean.mkAuxName baseName 1
      | some declName => Lean.mkAuxName (declName ++ baseName) 1
    let decl := Declaration.defnDecl {
      name := auxName, levelParams := [], type, value
      hints := .abbrev
      safety := .safe
    }
    addAndCompile decl
    pure auxName

namespace Tactic

syntax (name := absorb) "absorb" "(" term ", " term ")" : tactic

open Lean.Elab Tactic in
@[tactic absorb] def evalAbsorb : Tactic := fun stx =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    let zero ← elabTerm stx[2] none
    let op ← elabTerm stx[4] none
    Builtin.absorb mv zero op
    replaceMainGoal []

syntax (name := nativeAbsorb) "native_absorb" "(" term ", " term ")" : tactic

open Lean.Elab Tactic in
@[tactic nativeAbsorb] def evalNativeAbsorb : Tactic := fun stx =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    let zero ← elabTerm stx[2] none
    let op ← elabTerm stx[4] none
    Builtin.nativeAbsorb mv zero op
    replaceMainGoal []

end Smt.Reconstruct.Builtin.Tactic

example (x y z : Prop) : ((x ∧ y) ∧ z ∧ (False ∧ (True ∨ False))) = False := by
  native_absorb (False, And)

example (x y z : Int) : 1 * (x + y) * z * 0 = 0 := by
  absorb ((0 : Int), @HMul.hMul Int Int Int _)

example (x y z : Int) : 1 * (x + y) * z * 0 = 0 := by
  native_absorb ((0 : Int), @HMul.hMul Int Int Int _)

example (x y z : BitVec 32) : 1 &&& (x &&& y) &&& z &&& 0 = 0 := by
  absorb ((0 : BitVec 32), @HAnd.hAnd (BitVec 32) (BitVec 32) (BitVec 32) _)

example (x y z : BitVec 32) : 1 &&& (x &&& y) &&& z &&& 0#32 = 0#32 := by
  absorb (0#32, @HAnd.hAnd (BitVec 32) (BitVec 32) (BitVec 32) _)
