import Lean

namespace Lean.Meta.AC

open Lean.Elab Tactic

def traceACRflTop (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

/-- Similar to `rewriteUnnormalized`, but rewrite is only applied at the top level. -/
def rewriteUnnormalizedTop (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.acRflTop traceACRflTop do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[ac_rfl_top] expected a top level equality with AC operator on lhs and/or rhs, got {← mv.getType}"
  let (nl, pl) ← normalize l
  let (nr, pr) ← normalize r
  if nl == r then
    let some pl := pl | throwError "[ac_rfl_top] expected {l} to have an AC operator"
    let hl ← Meta.mkFreshExprMVar (← mkEq l nl)
    hl.mvarId!.assign pl
    let rl ← mv.rewrite (← mv.getType) hl false { occs := .pos [1] }
    let mv ← mv.replaceTargetEq rl.eNew rl.eqProof
    mv.refl
  else if l == nr then
    let some pr := pr | throwError "[ac_rfl_top] expected {r} to have an AC operator"
    let hr ← Meta.mkFreshExprMVar (← mkEq r nr)
    hr.mvarId!.assign pr
    let rr ← mv.rewrite (← mv.getType) hr false { occs := .pos [1] }
    let mv ← mv.replaceTargetEq rr.eNew rr.eqProof
    mv.refl
  else
    let some pl := pl | throwError "[ac_rfl_top] expected {l} to have an AC operator"
    let hl ← Meta.mkFreshExprMVar (← mkEq l nl)
    hl.mvarId!.assign pl
    let rl ← mv.rewrite (← mv.getType) hl false { occs := .pos [1] }
    let mv ← mv.replaceTargetEq rl.eNew rl.eqProof
    let some pr := pr | throwError "[ac_rfl_top] expected {r} to have an AC operator"
    let hr ← Meta.mkFreshExprMVar (← mkEq r nr)
    hr.mvarId!.assign pr
    let rr ← mv.rewrite (← mv.getType) hr false { occs := .pos [1] }
    let mv ← mv.replaceTargetEq rr.eNew rr.eqProof
    mv.refl
where
  normalize (e : Expr) : MetaM (Expr × Option Expr) := do
    let bin op l r := e | return (e, none)
    let some pc ← preContext op | return (e, none)
    let (p, ne) ← buildNormProof pc l r
    return (ne, some p)

syntax (name := ac_rfl_top) "ac_rfl_top" : tactic

@[tactic ac_rfl_top] def evalacRflTop : Lean.Elab.Tactic.Tactic := fun _ => do
  let goal ← getMainGoal
  goal.withContext <| rewriteUnnormalizedTop goal

private instance : Std.Associative (α := Nat) (.+.) := ⟨Nat.add_assoc⟩
private instance : Std.Commutative (α := Nat) (.+.) := ⟨Nat.add_comm⟩

example (a b c d : Nat) : 2 * (a + b + c + d) = 2 * (d + (b + c) + a) := by
  try ac_rfl_top
  ac_rfl

example (a b c d : Nat) : a + b + c + d + (2 * (a + b)) = d + (b + c) + a + (2 * (b + a)) := by
  try ac_rfl_top
  ac_rfl

example (a b c d : Nat) : a + b + c + d + (a + b) = d + (b + c) + a + (b + a) := by
  ac_rfl

end Lean.Meta.AC
