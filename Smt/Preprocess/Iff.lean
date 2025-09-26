/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Tomaz Gomes Mascarenhas
-/

import Smt.Preprocess.Basic
import Qq

namespace Smt.Preprocess

open Lean Qq

theorem iff_eq_eq : (p ↔ q) = (p = q) := propext ⟨propext, (· ▸ ⟨(·), (·)⟩)⟩

theorem eq_resolve {p q : Prop} (hp : p) (hpq : p = q) : q := hpq ▸ hp

def replaceIff (e : Expr) : MetaM Expr :=
  let f e :=
    if let some ((l : Q(Prop)), (r : Q(Prop))) := e.app2? ``Iff then
      q($l = $r)
    else
      none
  Meta.mkAppM ``Eq #[e, e.replace f]

def containsIff (e : Expr) : Bool :=
  (Expr.const ``Iff []).occurs e

def elimIff (mv : MVarId) (hs : Array Expr) : MetaM Result := mv.withContext do
  let t ← instantiateMVars (← mv.getType)
  let ts ← hs.mapM (Meta.inferType · >>= instantiateMVars)
  if !(containsIff t || ts.any containsIff) then
    return { map := Std.HashMap.insertMany ∅ (hs.zip (hs.map .singleton)), hs, mv }
  let simpTheorems ← #[``eq_self, ``iff_eq_eq].foldlM (·.addConst ·) ({} : Meta.SimpTheorems)
  let simpTheorems := #[simpTheorems]
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx ← Meta.Simp.mkContext {} simpTheorems congrTheorems
  let (hs', mv') ← elimIffLocalDecls mv hs.toList ctx #[]
  let mv' ← elimIffTarget mv' ctx
  return { map := Std.HashMap.insertMany ∅ (hs'.zip (hs.map .singleton)), hs := hs', mv := mv' }
where
  elimIffLocalDecls mv hs ctx hs' := do match hs with
    | [] => return (hs', mv)
    | h :: hs =>
      let type ← Meta.inferType h
      let eq ← replaceIff (← instantiateMVars type)
      let (_, l, r) := eq.eq?.get!
      if l == r then
        elimIffLocalDecls mv hs ctx (hs'.push h)
      else
        let (res, _) ← Meta.simp eq ctx
        let h' := mkApp4 (.const ``eq_resolve []) l r h (mkOfEqTrue eq (← res.getProof))
        if let .some fv := h.fvarId? then
          let res ← mv.replace fv h' (.some r)
          let hs' := hs'.map res.subst.apply
          let hs := hs.map res.subst.apply
          res.mvarId.withContext (elimIffLocalDecls res.mvarId hs ctx (hs'.push (.fvar res.fvarId)))
        else
          elimIffLocalDecls mv hs ctx (hs'.push h')
      termination_by hs.length
  elimIffTarget mv ctx := mv.withContext do
    let eq ← replaceIff (← instantiateMVars (← mv.getType))
    let (res, _) ← Meta.simp eq ctx
    if res.expr.isTrue then
      mv.replaceTargetEq eq.appArg! (mkOfEqTrue eq (← res.getProof))
    else
      return mv
  mkOfEqTrue p hpt :=
    mkApp2 (.const ``of_eq_true []) p hpt

end Smt.Preprocess
