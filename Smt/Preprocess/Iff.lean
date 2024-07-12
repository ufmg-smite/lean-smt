/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Tomaz Gomes Mascarenhas
-/

import Lean
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

def elimIff (mv : MVarId) (hs : List Expr) : MetaM (List Expr × MVarId) := mv.withContext do
  let simpTheorems ← #[``eq_self, ``iff_eq_eq].foldlM (·.addConst ·) ({} : Meta.SimpTheorems)
  let simpTheorems := #[simpTheorems]
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx := { simpTheorems, congrTheorems }
  let (hs, mv) ← elimIffLocalDecls mv hs ctx
  let mv ← elimIffTarget mv ctx
  return (hs, mv)
where
  elimIffLocalDecls mv hs ctx := mv.withContext do
    let mut newHs := []
    let mut toAssert := #[]
    for h in hs do
      let type ← Meta.inferType h
      let eq ← replaceIff (← instantiateMVars type)
      let (_, l, r) := eq.eq?.get!
      if l == r then
        newHs := h :: newHs
      else
        let userName ← if h.isFVar then h.fvarId!.getUserName else Lean.mkFreshId
        let type := r
        let (r, _) ←  Meta.simp eq ctx
        let value ←  Meta.mkAppM ``eq_resolve #[h, ← Meta.mkOfEqTrue (← r.getProof)]
        toAssert := toAssert.push { userName, type, value }
    let (fvs, mv) ← mv.assertHypotheses toAssert
    newHs := newHs.reverse ++ (fvs.map (.fvar ·)).toList
    return (newHs, mv)
  elimIffTarget mv ctx := mv.withContext do
    let eq ← replaceIff (← instantiateMVars (← mv.getType))
    let (r, _) ←  Meta.simp eq ctx
    if r.expr.isTrue then
      mv.replaceTargetEq eq.appArg! (← Meta.mkOfEqTrue (← r.getProof))
    else
      return mv

end Smt.Preprocess
