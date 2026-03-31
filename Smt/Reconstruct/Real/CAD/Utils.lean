import Lean

open Lean Elab Tactic ToExpr Meta

/-- Given:
  - `h1 : P`  (a proof of some proposition)
  - `h2 : a = b`  (a proof of some equality)
  Produces `h1' : P[a ↦ b]`, i.e. `h1` rewritten left-to-right by `h2` everywhere. -/
def rewriteWithEq (h1 h2 : Expr) : MetaM Expr := do
  let prop ← inferType h1
  let eqType ← inferType h2
  let some (α, a, b) := eqType.eq?
    | throwError "rewriteWithEq: h2 is not a proof of an equality, got {eqType}"
  let motive ← kabstract prop a
  if motive == prop then
    return h1
  let newProp := motive.instantiate1 b
  let motiveExpr := mkLambda `x .default α motive
  let h1' ← mkAppOptM ``Eq.subst #[none, motiveExpr, a, b, h2, h1]
  let h1'Type ← inferType h1'
  unless ← isDefEq h1'Type newProp do
    throwError "rewriteWithEq: type mismatch, expected {newProp} but got {h1'Type}"
  return h1'

