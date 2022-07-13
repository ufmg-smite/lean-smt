import Lean.Meta.Basic

namespace Smt
open Lean Meta

/-- Controls which rules are applied during WHNF and reduction. -/
structure Config where
  /-- When `zeta` is off, we add `let x : t := v; b` to the set of WHNFs.

  This requires an extra congruence rule in full reduction:
  ```lean
  Γ ⊢ t ⤳ t'  Γ ⊢ v ⤳ v'  Γ, x : t ⊢ b ⤳ b'
  --------------------------------------------
  Γ ⊢ let x : t := v; b ⤳ let x : t' := v'; b'
  ``` -/
  zeta : Bool := true
  beta : Bool := true
  eta  : Bool := true
  iota : Bool := true
  proj : Bool := true
  /-- Add the WHNF rule
  ```lean
  Γ ⊢ ELIM[let x : t := v; b] ⤳ let x : t := v; ELIM[b]
  ```
  where `ELIM` is either a function application or a projection. -/
  letPushElim : Bool := false
  /-- Add the WHNF rule
  ```lean
  Γ ⊢ e : α  Γ ⊢ e ⤳ e'
  -------------------------------
  Γ ⊢ f e ⤳ let x : α := e'; f x
  ```
  which can be combined with `zeta := false` to hoist arguments into let-bindings instead of substitution.
  When used correctly, this can give us graph-like sharing in the (weak-head) normalized expression. -/
  letPullArgs : Bool := false

abbrev ReductionM := ReaderT Config MetaM

initialize whnfRef : IO.Ref (Expr → ReductionM Expr) ← 
  IO.mkRef fun e => return e

def whnf (e : Expr) : ReductionM Expr := do
  let fn ← whnfRef.get
  fn e

def whnfD (e : Expr) : ReductionM Expr :=
  withTransparency TransparencyMode.default <| whnf e

end Smt
