import Lean.Meta.Basic

namespace Smt
open Lean Meta

/-- Controls which rules are applied during WHNF and reduction. -/
structure Config where
  zeta : Bool := true
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
