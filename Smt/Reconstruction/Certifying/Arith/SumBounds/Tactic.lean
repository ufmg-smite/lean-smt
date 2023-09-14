/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Reconstruction.Certifying.Arith.SumBounds.Lemmas
import Smt.Reconstruction.Certifying.Arith.SumBounds.Instances
import Smt.Reconstruction.Certifying.Arith.TightBounds.Lemmas
import Smt.Reconstruction.Certifying.Util

open Lean hiding Rat
open Meta Elab.Tactic Expr

namespace Smt.Reconstruction.Certifying

theorem castLT.NatRat : ∀ {a b : Nat}, a < b → Rat.ofInt (Int.ofNat a) < Rat.ofInt (Int.ofNat b) := by
  intros a b
  simp

theorem castLT.NatInt : ∀ {a b : Nat}, a < b → Int.ofNat a < Int.ofNat b := by
  intros a b
  simp

theorem castLE.NatRat : ∀ {a b : Nat}, a ≤ b → Rat.ofInt (Int.ofNat a) ≤ Rat.ofInt (Int.ofNat b) := by
  intros a b
  simp

theorem castLE.NatInt : ∀ {a b : Nat}, a ≤ b → Int.ofNat a ≤ Int.ofNat b := by
  intros a b
  simp

theorem castEQ.NatRat : ∀ {a b : Nat}, a = b → Rat.ofInt (Int.ofNat a) = Rat.ofInt (Int.ofNat b) := by
  intros a b h
  rw [h]

theorem castEQ.NatInt : ∀ {a b : Nat}, a = b → Int.ofNat a = Int.ofNat b := by
  intros a b h
  rw [h]

theorem Int.castEQ : ∀ {a b : Int}, a = b → Rat.ofInt a = Rat.ofInt b := by
  intros a b h
  rw [h]

def getCastRelThm (rel : Name) : Name :=
  match rel with
  | ``LT.lt => `castLT
  | ``LE.le => `castLE
  | ``Eq    => `castEQ
  | _ => `unreachable

def combineBounds (mvar : MVarId) : Expr → Expr → MetaM Expr := fun h₁ h₂ =>
  mvar.withContext do
    let t₁ ← expandLet (← inferType h₁)
    let rel₁ ← getOp t₁
    let t₂ ← expandLet (← inferType h₂)
    let rel₂ ← getOp t₂
    let tp₁ ← getOpType t₁
    let tp₂ ← getOpType t₂
    let (h₁, h₂) ←
      match tp₁, tp₂ with
      | const `Nat .., const `Int .. =>
        let thm := getCastRelThm rel₁ ++ `NatInt
        pure (← mkAppM thm #[h₁], h₂)
      | const `Nat .., const `Rat .. =>
        let thm := getCastRelThm rel₁ ++ `NatRat
        pure (← mkAppM thm #[h₁], h₂)
      | const `Int .., const `Rat .. =>
        let thm := getCastRelThm rel₁ ++ `IntRat
        pure (← mkAppM thm #[h₁], h₂)
      | const `Int .., const `Nat .. =>
        let thm := getCastRelThm rel₂ ++ `NatInt
        pure (h₁, ← mkAppM thm #[h₂])
      | const `Rat .., const `Nat .. =>
        let thm := getCastRelThm rel₂ ++ `NatRat
        pure (h₁, ← mkAppM thm #[h₂])
      | const `Rat .., const `Int .. =>
        let thm := getCastRelThm rel₂ ++ `IntRat
        pure (h₁, ← mkAppM thm #[h₂])
      | _, _ => pure (h₁, h₂)
    let thmName : Name ←
      match rel₂, rel₁ with
      | ``LT.lt , ``LT.lt => pure ``sumBounds₁
      | ``LT.lt , ``LE.le => pure ``sumBounds₂
      | ``LT.lt , ``Eq    => pure ``sumBounds₃
      | ``LE.le , ``LT.lt => pure ``sumBounds₄
      | ``LE.le , ``LE.le => pure ``sumBounds₅
      | ``LE.le , ``Eq    => pure ``sumBounds₆ 
      | ``Eq    , ``LT.lt => pure ``sumBounds₇
      | ``Eq    , ``LE.le => pure ``sumBounds₈
      | ``Eq    , ``Eq    => pure ``sumBounds₉
      | _      , _      => throwError "[sumBounds] invalid operation"
    mkAppM thmName #[h₂, h₁]
where 
  getOpType : Expr → MetaM Expr
  | app (Expr.const ``Not ..) e' => getOpType e'
  | app (app (app (app (app (Expr.const _ ..) tp) ..) ..) ..) .. => pure tp
  | app (app (app (app (Expr.const _ ..) tp) ..) ..) .. => pure tp
  | app (app (app (Expr.const _ ..) tp) ..) .. => pure tp
  | _ => throwError "[getOp] invalid parameter"

def sumBoundsMeta (mvar : MVarId) (h : Expr) (hs : List Expr) (name : Name)
    : MetaM MVarId :=
  mvar.withContext do
    go h hs
where
  go : Expr → List Expr → MetaM MVarId
    | acc, [] => do
      let type ← inferType acc
      let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name type acc
      return mvar'
    | acc, h::hs => do
      let acc ← combineBounds mvar acc h
      go acc hs

syntax (name := sumBounds) "sumBounds" "[" term,* "]" : tactic

def parseSumBounds : Syntax → TacticM (List Expr)
  | `(tactic| sumBounds [$[$hs],*]) =>
    hs.toList.mapM (fun stx => do expandLet (← elabTerm stx.raw none))
  | _ => throwError "[sumBounds]: expects a list of premisses"

@[tactic sumBounds] def evalSumBounds : Tactic := fun stx =>
  withMainContext do
    trace[smt.debug] m!"[sumBounds] start time: {← IO.monoNanosNow}ns"
    let (h, hs) ←
      match ← parseSumBounds stx with
      | h::hs =>
        let h'::hs' := List.reverse (h::hs) | throwError "unreachable"
        pure (h', hs')
      | [] => throwError "[sumBounds]: empty list of premisses"
    let mvar ← getMainGoal
    let fname ← mkFreshId
    let mvar' ← sumBoundsMeta mvar h hs fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.debug] m!"[sumBounds] end time: {← IO.monoNanosNow}ns"

end Smt.Reconstruction.Certifying

