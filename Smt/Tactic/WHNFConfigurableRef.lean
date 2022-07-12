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
  /-- The WHNF rule
  ```lean
  Γ ⊢ ELIM[let x : t := v; b] ⤳ let x : t := v; ELIM[b]
  ```
  where `ELIM` is either a function application or a projection. -/
  pushElim : Bool := false
  beta : Bool := true
  eta  : Bool := true
  iota : Bool := true
  proj : Bool := true

abbrev ReductionM := ReaderT Config MetaM

initialize whnfRef : IO.Ref (Expr → ReductionM Expr) ← 
  IO.mkRef fun e => return e

def whnf (e : Expr) : ReductionM Expr := do
  let fn ← whnfRef.get
  fn e

def whnfD (e : Expr) : ReductionM Expr :=
  withTransparency TransparencyMode.default <| whnf e

end Smt
