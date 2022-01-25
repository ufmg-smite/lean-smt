import Lean
import Smt.Transformer

namespace Smt.String

open Lean
open Lean.Expr
open Smt.Transformer

@[Smt] def markStringGetOp : Transformer := fun e => do match e with
  | a@(app (app (const `String.getOp ..) f _) e _)  =>
    addMark a (mkApp (mkConst `str.to_code) (mkApp2 (mkConst `str.at) f e))
    markStringGetOp f
    markStringGetOp e
  | app f e _       => markStringGetOp f; markStringGetOp e
  | lam _ _ b _     => markStringGetOp b
  | mdata _ e _     => markStringGetOp e
  | proj _ _ e _    => markStringGetOp e
  | letE _ _ v b _  => markStringGetOp v; markStringGetOp b
  | forallE _ t b _ => markStringGetOp t; markStringGetOp b
  | _               => ()

@[Smt] def markStringContains : Transformer := fun e => do match e with
  | a@(app (app (const `String.contains ..) f _) e _)  =>
    addMark a (mkApp2 (mkConst `str.contains) f (mkApp (mkConst `str.from_code) e))
    markStringGetOp f
    markStringGetOp e
  | app f e _       => markStringContains f; markStringContains e
  | lam _ _ b _     => markStringContains b
  | mdata _ e _     => markStringContains e
  | proj _ _ e _    => markStringContains e
  | letE _ _ v b _  => markStringContains v; markStringContains b
  | forallE _ t b _ => markStringContains t; markStringContains b
  | _               => ()

end Smt.String
