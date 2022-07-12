import Lean.Meta.Basic

namespace Smt
open Lean Meta

initialize whnfRef : IO.Ref (Expr → MetaM Expr) ← 
  IO.mkRef fun e => return e

def whnf (e : Expr) : MetaM Expr := do
  let fn ← whnfRef.get
  fn e

def whnfD (e : Expr) : MetaM Expr :=
  withTransparency TransparencyMode.default <| whnf e

end Smt
