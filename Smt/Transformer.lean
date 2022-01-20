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

/-- Monad for transforming expressions. Keeps track of sub-expressions marked
    for removal/replacement. -/
abbrev TransformerM := StateT (HashMap Expr (Option Expr)) MetaM

/-- Type of functions that mark expressions. -/
abbrev Transformer := Expr → TransformerM Unit

namespace Transformer

/-- Mark `e` for removal (if `e'` is `none`) or replacement with `e'`. -/
def addMark (e : Expr) (e' : Option Expr) : TransformerM Unit :=
  get >>= fun map => set (map.insert e e')

/-- Is `e` marked for removal/replacement? -/
def isMarked (e : Expr) : TransformerM Bool :=
  get >>= fun map => map.contains e

/-- Get `e`'s replacement, if it exists. -/
def getReplacement! (e : Expr) : TransformerM (Option Expr) :=
  get >>= fun map => map.find! e

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
partial def replaceMarked (e : Expr) : TransformerM (Option Expr) := do
  match ← isMarked e with
  | true => match ← getReplacement! e with
    | none    => none             -- Remove `e`.
    | some e' => replaceMarked e' -- Replace `e` with `e'` and process `e'`.
  | false    => match e with
    | app f e d       => match ← replaceMarked f, ← replaceMarked e with
       -- Replace `(APP f e)` with `(APP f' e')`.
      | some f', some e' => mkApp f' e'
       -- Replace `(APP f e)` with `e'`.
      | none   , some e' => e'
       -- Replace `(APP f e)` with `f'`.
      | some f', none    => f'
       -- Remove `(APP f e)`.
      | none   , none    => none
    | lam n t b d     => match ← replaceMarked b with
      | none   => none
      | some b => mkLambda n d.binderInfo t b
    | forallE n t b d => match ← replaceMarked b with
      | some b => mkForall n d.binderInfo t b
      | _      => none
    | letE n t v b d  => match ← replaceMarked t,
                               ← replaceMarked v,
                               ← replaceMarked b with
      | some t, some v, some b => mkLet n t v b
      | _     , _     , _      => none
    | mdata m e s     => match ← replaceMarked e with
      | none => none
      | some e => mkMData m e
    | proj s i e d    => match ← replaceMarked e with
      | none => none
      | some e => mkProj s i e
    | e               => e

/-- Print an adjacency list of exprs using AST printer for `Expr`. -/
def List.toString (es : List (Expr × (Option Expr))) := s!"[" ++ String.intercalate ", " (es.map helper) ++ "]"
  where
    helper : Expr × (Option Expr) → String
    | (e, o) => s!"({exprToString e},{o.format.pretty})"

private unsafe def getTransformersUnsafe : MetaM (List Transformer) := do
  let env ← getEnv
  let names := (smtExt.getState env).toList
  trace[Smt.debug.attr] "Transformers: {names}"
  let mut transformers := []
  for name in names do
    let fn ← IO.ofExcept <| Id.run <| ExceptT.run <|
      env.evalConst Transformer Options.empty name
    transformers := fn :: transformers
  transformers

/-- Returns the list of transformers maintained by `smtExt` in the current
    Lean environment. -/
@[implementedBy getTransformersUnsafe]
constant getTransformers : MetaM (List Transformer)

/-- Pre-processes `e` and returns the resulting expr. -/
def preprocessExpr (e : Expr) : MetaM Expr := do
  -- Print the `e` before the preprocessing step.
  trace[Smt.debug.transformer] "Before: {exprToString e}"
  let mut es ← HashMap.empty
  -- Pass `e` through each pre-processing step to mark sub-exprs for removal or
  -- replacement. Note that each pass is passed the original expr `e` as an
  -- input. So, the order of the passes does not matter.
  for transformer in (← getTransformers) do
    (_, es) ← (transformer e).run es
  -- Print the exprs marked for removal/replacement.
  trace[Smt.debug.transformer] "marked: {es.toList.toString}"
  -- Make the replacements and print the result.
  match ← (replaceMarked e).run es with
    | (none  , _) => panic! "Error: Something went wrong..."
    | (some e, _) => trace[Smt.debug.transformer] "After: {exprToString e}"; e

/-- Converts a Lean expression into an SMT term. -/
partial def exprToTerm (e : Expr) : MetaM Term := do
  let e ← preprocessExpr e
  exprToTerm' e
  where
    exprToTerm' (e : Expr) : MetaM Term := do match e with
      | fvar id _           =>
        let n := (← Meta.getLocalDecl id).userName.toString
        Symbol n
      | e@(const n ..)      => Symbol (toString e)
      | sort l _ =>
        Symbol
          (if l.isZero then "Bool" else "Sort " ++ ⟨Nat.toDigits 10 l.depth⟩)
      | e@(forallE n s b _) =>
        if e.isArrow then
          Meta.forallTelescope e fun ss s => do
            let ss ← ss.mapM Meta.inferType
            ss.foldrM (fun d c => do Arrow (← exprToTerm' d) (← c))
                      (← exprToTerm' s)
        else
          Forall n.toString (← exprToTerm' s) <|
            ← Meta.forallBoundedTelescope e (some 1) (fun _ b => exprToTerm' b)
      | app (const `exists ..) (lam n t b d) _ =>
        Meta.withLocalDecl n d.binderInfo t fun x => do
        Exists n.toString (← exprToTerm' t) (← exprToTerm' (b.instantiate #[x]))
      | app f t _           => App (← exprToTerm' f) (← exprToTerm' t)
      | lit l _             => Literal (match l with
        | Literal.natVal n => ⟨Nat.toDigits 10 n⟩
        | Literal.strVal s => s!"\"{s}\"")
      | e                   => panic! "Unimplemented: " ++ exprToString e

end Smt.Transformer
