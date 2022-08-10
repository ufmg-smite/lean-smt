/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
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

abbrev ReductionM := ReaderT Config MetaM

initialize whnfRef : IO.Ref (Expr → ReductionM Expr) ← 
  IO.mkRef fun e => return e

def whnf (e : Expr) : ReductionM Expr := do
  let fn ← whnfRef.get
  fn e

def whnfD (e : Expr) : ReductionM Expr :=
  withTransparency TransparencyMode.default <| whnf e

end Smt
