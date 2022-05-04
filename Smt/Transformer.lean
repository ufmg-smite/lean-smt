import Lean
import Smt.Term
import Smt.Util
import Smt.Attribute

namespace Smt

open Lean
open Lean.Expr
open Smt.Attribute
open Smt.Term
open Smt.Util
open Std

/-- Type of functions that transform expressions. -/
abbrev Transformer := Expr → MetaM (Option Expr)

namespace Transformer

private unsafe def getTransformersUnsafe : MetaM (List Transformer) := do
  let env ← getEnv
  let names := (smtExt.getState env).toList
  trace[Smt.debug.attr] "Transformers: {names}"
  let mut transformers := []
  for name in names do
    let fn ← IO.ofExcept <| Id.run <| ExceptT.run <|
      env.evalConst Transformer Options.empty name
    transformers := fn :: transformers
  return transformers

/-- Returns the list of transformers maintained by `smtExt` in the current
    Lean environment. -/
@[implementedBy getTransformersUnsafe]
constant getTransformers : MetaM (List Transformer)

/-- Traverses `e` and replaces marked sub-exprs with corresponding exprs in `es`
    or removes them if there are no corresponding exprs to replace them with.
    The order of the replacements is done in a top-down depth-first order. For
    example, let that `e*` denote an expr `e` is marked for removal and `e*`
    denote `e` is marked for replacement with `e'`. Then given,
    `(APP (APP a b*) c+)`, this method will return `(APP a c')`. Note that this
    method also processes sub-exprs of `e'`. For example, `(FORALL _ p+ q)+`
    is replaced with `(Imp p' q)`. Some replacements and removals may return
    ill-formed exprs for SMT-LIBv2. It's the caller's responsibility to ensure
    that the replacement do not produce ill-formed exprs. -/
partial def applyTransformations : Transformer := fun e => do
  let ts ← getTransformers
  appTransforms' ts e
  where
    appTransforms' (ts : List Transformer) : Transformer := fun e => do
      for t in ts do
        match (← t e) with
        | none    => trace[Smt.debug.transformer] "({e}, none)"; return none
        | some e' =>
          if e' == e then continue
          else trace[Smt.debug.transformer] "({e}, {e'})"; return e'
      match e with
      | app f e _       => match ← appTransforms' ts f,
                                 ← appTransforms' ts e with
        -- Remove `(APP f e)`.
        | none   , none    => pure none
        -- Replace `(APP f e)` with `e'`.
        | none   , some e' => pure e'
        -- Replace `(APP f e)` with `f'`.
        | some f', none    => pure f'
        -- Replace `(APP f e)` with `(APP f' e')`.
        | some f', some e' => pure (mkApp f' e')
      | lam n t b d     =>
        let t' ← appTransforms' ts t
        let b' ← Meta.withLocalDecl n d.binderInfo t (appTransforms'' ts b)
        match t', b' with
        | some t', some b' => pure (mkLambda n d.binderInfo t' b')
        | _      , _       => pure none
      | forallE n t b d =>
        let t' ← appTransforms' ts t
        let b' ← Meta.withLocalDecl n d.binderInfo t (appTransforms'' ts b)
        match t', b' with
        | some t', some b' => pure (mkForall n d.binderInfo t' b')
        | _      , _       => pure none
      | letE n t v b d  =>
        let t' ← appTransforms' ts t
        let v' ← appTransforms' ts v
        let b' ← Meta.withLetDecl n t v (appTransforms'' ts b)
        match t', v', b' with
        | some t', some v' , some b' => pure (mkLet n t' v' b')
        | _      , _       , _       => pure none
      | mdata m e s     => match ← appTransforms' ts e with
        | none => pure none
        | some e => pure (mkMData m e)
      | proj s i e d    => match ← appTransforms' ts e with
        | none => pure none
        | some e => pure (mkProj s i e)
      | e               => pure e
    appTransforms'' ts b x := do
      let mut b' ← appTransforms' ts (b.instantiate #[x])
      if let some b'' := b' then
        b' := some (b''.abstract #[x])
      return b'

/-- Pre-processes `e` and returns the resulting expr. -/
def preprocessExpr (e : Expr) : MetaM Expr := do
  -- Print the `e` before the preprocessing step.
  trace[Smt.debug.transformer] "before: {exprToString e}"
  -- Pass `e` through each pre-processing step to mark sub-exprs for removal or
  -- replacement. Note that each pass is passed the original expr `e` as an
  -- input. So, the order of the passes does not matter.
  trace[Smt.debug.transformer] "marked:"
  let e' ← applyTransformations e
  -- Print the exprs marked for removal/replacement.
  -- Make the replacements and print the result.
  let (some e') := e'
    | panic! s!"Error: Something went wrong while transforming {e}"
  trace[Smt.debug.transformer] "after: {exprToString e'}"
  return e'

/-- Converts a Lean expression into an SMT term. -/
partial def exprToTerm (e : Expr) : MetaM Term := do
  let e ← preprocessExpr e
  exprToTerm' e
  where
    exprToTerm' (e : Expr) : MetaM Term := do match e with
      | fvar id _           =>
        let n := (← Meta.getLocalDecl id).userName.toString
        pure (Symbol n)
      | e@(const n ..)      => pure (Symbol (toString e))
      | sort l _ =>
        pure $ Symbol
          (if l.isZero then "Bool" else "Sort " ++ ⟨Nat.toDigits 10 l.depth⟩)
      | e@(forallE n s b _) =>
        if e.isArrow then
          Meta.forallTelescope e fun ss s => do
            let ss ← ss.mapM Meta.inferType
            ss.foldrM (fun d c => do return Arrow (← exprToTerm' d) c)
                      (← exprToTerm' s)
        else
          pure $ Forall n.toString (← exprToTerm' s) <|
            ← Meta.forallBoundedTelescope e (some 1) (fun _ b => exprToTerm' b)
      | app (const `exists ..) (lam n t b d) _ =>
        Meta.withLocalDecl n d.binderInfo t fun x => do
        return Exists n.toString (← exprToTerm' t)
                                 (← exprToTerm' (b.instantiate #[x]))
      | app f t _           => pure $ App (← exprToTerm' f) (← exprToTerm' t)
      | lit l _             => pure $ Literal (match l with
        | Literal.natVal n => ⟨Nat.toDigits 10 n⟩
        | Literal.strVal s => s!"\"{s}\"")
      | e                   => panic! "Unimplemented: " ++ exprToString e

end Smt.Transformer
