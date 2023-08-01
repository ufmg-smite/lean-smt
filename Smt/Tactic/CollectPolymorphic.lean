import Lean

import Smt.Tactic.Concretize

open Lean Elab Tactic Meta Expr

def isPolymorphicConst (e : Expr) : MetaM Bool := do
  let t ← inferType e
  match t with
    | .forallE _ (.sort (.succ .zero)) _ _ => return true
    | _ => return false

def collectPolymorphicNames : Expr → MetaM NameSet
  | .app f x => do
    let rc₁ ← collectPolymorphicNames f
    let rc₂ ← collectPolymorphicNames x
    return RBTree.union rc₁ rc₂
  | e@(.const nm _) => do
    if ← isPolymorphicConst e then
      return NameSet.insert NameSet.empty nm
    else return NameSet.empty
  | .lam _ _ body _ => collectPolymorphicNames body
  | .forallE _ _ body _ => collectPolymorphicNames body
  | .letE _ _ value body _ => do
    let rc₁ ← collectPolymorphicNames value
    let rc₂ ← collectPolymorphicNames body
    return RBTree.union rc₁ rc₂
  | _ => return NameSet.empty

syntax (name := monomorphize) "monomorphize" : tactic

@[tactic monomorphize] def evalMonomorphize : Tactic := fun _ =>
  withMainContext do
    let g ← getMainTarget
    let nms ← collectPolymorphicNames g
    for nm in nms do
      logInfo m!"nm = {nm}"
    logInfo m!"done"
  /- evalConcretize -/
  /-   |>.run' { visitSet := #[.goal] } -/
  /-   |>.run { concretizeSet } -/

