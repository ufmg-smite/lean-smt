import Lean
import Smt.Term
import Smt.Util

namespace Smt.Transformer

open Lean
open Lean.Expr
open Smt.Term
open Smt.Util
open Std

/-- Inserts entries in second hashmap into the first one. -/
def Std.HashMap.insertAll [BEq α] [Hashable α] :
  HashMap α β → HashMap α β → HashMap α β := HashMap.fold HashMap.insert

/-- Convenience `++` syntax for `Std.HashMap.insertAll`. -/
instance [BEq α] [Hashable α] : Append (HashMap α β) := ⟨Std.HashMap.insertAll⟩

/-- Traverses `e` and marks type arguments in apps for removal. For example,
    given `(App (App (App Eq Prop) p) q)`, this method should mark `Prop` for
    removal and the resulting expr will be `(App (App Eq p) q)`. -/
partial def markTypeArgs (e : Expr) : MetaM (HashMap Expr (Option Expr)) :=
  markTypeArgs' #[] e
  where
    markTypeArgs' xs e := do match e with
      | app f e d       => if ← hasValidSort (e.instantiate xs) then
                             (← markTypeArgs' xs f) ++ (← markTypeArgs' xs e)
                           else (← markTypeArgs' xs f).insert e none
      | lam n t b d     => (← markTypeArgs' xs t)
        ++ (← Meta.withLocalDecl n d.binderInfo t
             (fun x => markTypeArgs' (xs.push x) b))
      | forallE n t b d => (← markTypeArgs' xs t)
        ++ (← Meta.withLocalDecl n d.binderInfo t
             (fun x => markTypeArgs' (xs.push x) b))
      | letE n t v b d  => (← markTypeArgs' xs t) ++ (← markTypeArgs' xs v)
      ++ (← Meta.withLetDecl n t v (fun x => markTypeArgs' (xs.push x) b))
      | mdata m e s     => markTypeArgs' xs e
      | proj s i e d    => markTypeArgs' xs e
      | e               => HashMap.empty
    -- Returns the whether or not we should add `e` to the argument list
    -- (i.e., skip implicit sort arguments).
    hasValidSort (e : Expr) : MetaM Bool := do
      let type ← Meta.inferType e
      match type with
      | sort l ..  => l.isZero
      | forallE .. => false    -- All arguments must be first order.
      | _          => true

/-- Traverses `e` and marks type class instantiations in apps for removal. For
    example, given `(APP instOfNatNat (LIT 1))`, this method should mark
    `instOfNatNat` for removal and the resulting expr will be `(LIT 1)`. -/
partial def markInstArgs (e : Expr) : MetaM (HashMap Expr (Option Expr)) :=
  do match e with
  | app f e d       => if ¬isInst e then
                         (← markInstArgs f) ++ (← markInstArgs e)
                       else (← markInstArgs f).insert e none
  | lam n t b d     => (← markInstArgs t) ++ (← markInstArgs b)
  | forallE n t b d => (← markInstArgs t) ++ (← markInstArgs b)
  | letE n t v b d  => (← markInstArgs t) ++ (← markInstArgs v)
                                          ++ (← markInstArgs b)
  | mdata m e s     => markInstArgs e
  | proj s i e d    => markInstArgs e
  | e               => HashMap.empty
  where
    -- Checks whether `e` is a type class instantiation.
    -- TODO: Too fragile, replace with better checks.
    isInst (e : Expr) : Bool := match e with
    | app (app (const n ..) ..) .. => n.toString.startsWith "inst"
    | _                            => false

/-- Traverses `e` and marks `Nat` constructors `Nat.zero` and `Nat.succ n` for
    replacement with `0` and `(+ n 1)`. -/
partial def markNatCons (e : Expr) : MetaM (HashMap Expr (Option Expr)) :=
  do match e with
  | a@(app (const n ..) e d) =>
    if n.toString = "Nat.succ" then
      (← markNatCons e).insert a <| mkApp2
        (mkConst <| (Name.mkSimple "HAdd").mkStr "hAdd")
        e
        (mkLit (Literal.natVal 1))
    else ← markNatCons e
  | app f e d                => (← markNatCons f)
    ++ (← markNatCons e)
  | lam n t b d              => (← markNatCons t) ++ (← markNatCons b)
  | forallE n t b d          => (← markNatCons t) ++ (← markNatCons b)
  | letE n t v b d           => (← markNatCons t) ++ (← markNatCons v)
                                                  ++ (← markNatCons b)
  | mdata m e s              => markNatCons e
  | proj s i e d             => markNatCons e
  | e@(const n ..)           =>
    if n.toString == "Nat.zero" then
      return HashMap.empty.insert e (mkLit (Literal.natVal 0))
    else HashMap.empty
  | e                        => HashMap.empty

/-- Traverses `e` and marks type casts of literals to `Nat` for replacement with
    just the literals. For example, given
    `(app (app (app (OfNat.ofNat ..) ..) (LIT 0) ..) ..)`, this method should
    mark the whole expr for replacement with just `(LIT 0)`. -/
partial def markNatLiterals (e : Expr) : MetaM (HashMap Expr (Option Expr)) :=
  do match e with
  | a@(app f e d)   => match toLiteral f with
    | none   => (← markNatLiterals f) ++ (← markNatLiterals e)
    | some l => return HashMap.empty.insert a l
  | lam n t b d     => (← markNatLiterals t) ++ (← markNatLiterals b)
  | forallE n t b d => (← markNatLiterals t) ++ (← markNatLiterals b)
  | letE n t v b d  => (← markNatLiterals t) ++ (← markNatLiterals v)
                                             ++ (← markNatLiterals b)
  | mdata m e s     => markNatLiterals e
  | proj s i e d    => markNatLiterals e
  | e               => HashMap.empty
  where
    toLiteral : Expr → Option Expr
      | app (app (const n ..) ..) l .. =>
        if n.toString = "OfNat.ofNat" then l else none
      | e                              => none

/-- Traverses `e` and marks arrows for replacement with `Imp`. For example,
    given `(FORALL _ p q)`, this method should mark the given expr for
    replacement with `(Imp p q)`. The replacement is done at this stage because
    `e` is a well-typed Lean term. So, we can ask Lean to infer the type of `p`,
    which is not possible after the pre-processing step. -/
partial def markImps (e : Expr) : MetaM (HashMap Expr (Option Expr)) :=
  markImps' #[] e
  where
    markImps' xs e := do match e with
      | app f e d           => (← markImps' xs f) ++ (← markImps' xs e)
      | lam n t b d         => (← markImps' xs t)
        ++ (← Meta.withLocalDecl n d.binderInfo t
            (fun x => markImps' (xs.push x) b))
      | e@(forallE n t b d) =>
        if (e.instantiate xs).isArrow ∧
           (← Meta.inferType (t.instantiate xs)).isProp then
          ((← markImps' xs t) ++
            (← markImps' xs b)).insert e (mkApp2 imp t (b.lowerLooseBVars 1 1))
        else (← markImps' xs t)
          ++ (← Meta.withLocalDecl n d.binderInfo t
               (fun x => markImps' (xs.push x) b))
      | letE n t v b d      => (← markImps' xs t) ++ (← markImps' xs v)
        ++ (← Meta.withLetDecl n t v (fun x => markImps' (xs.push x) b))
      | mdata m e s         => markImps' xs e
      | proj s i e d        => markImps' xs e
      | e                   => HashMap.empty
    imp := mkConst (Name.mkSimple "Imp")

partial def markNatForalls (e : Expr) : MetaM (HashMap Expr (Option Expr)) :=
  markImps' #[] e
  where
    markImps' xs e := do match e with
      | app f e d           => (← markImps' xs f) ++ (← markImps' xs e)
      | lam n t b d         => (← markImps' xs t)
        ++ (← Meta.withLocalDecl n d.binderInfo t
            (fun x => markImps' (xs.push x) b))
      | e@(forallE n t@(const `Nat ..) b d) =>
        if ¬(e.instantiate xs).isArrow then
          (← markImps' xs t).insert e (mkForall n d.binderInfo t (imp b))
            ++ (← Meta.withLocalDecl n d.binderInfo t
                (fun x => markImps' (xs.push x) b))
        else (← markImps' xs t)
          ++ (← Meta.withLocalDecl n d.binderInfo t
               (fun x => markImps' (xs.push x) b))
      | e@(forallE n t b d) => (← markImps' xs t)
          ++ (← Meta.withLocalDecl n d.binderInfo t
               (fun x => markImps' (xs.push x) b))
      | letE n t v b d      => (← markImps' xs t) ++ (← markImps' xs v)
        ++ (← Meta.withLetDecl n t v (fun x => markImps' (xs.push x) b))
      | mdata m e s         => markImps' xs e
      | proj s i e d        => markImps' xs e
      | e                   => HashMap.empty
    imp e := mkApp2 (mkConst `Imp) (mkApp2 (mkConst `GE.ge)
                                           (mkBVar 0)
                                           (mkLit (Literal.natVal 0)))
                    e

/-- Traverses `e` and replaces marked sub-exprs with corresponding exprs in `es`
    or removes them if there are no corresponding exprs to replace them with.
    The order of the replacements is done in a top-down depth-first order. For
    example, let that `e*` denote an expr `e` is marked for removal and `e*` denote `e` is marked for replacement with `e'`. Then given,
    `(APP (APP a b*) c+)`, this method will return `(APP a c')`. Note that
    this method also processes sub-exprs of `e'`. For example,
    `(FORALL _ p+ q)+` is replaced with `(Imp p' q)`. Some replacements and
    removals may return ill-formed exprs for SMT-LIBv2. It's the caller's
    responsibility to ensure that the replacement do not produce ill-formed
    exprs. -/
partial def replaceMarked (e : Expr) (es : HashMap Expr (Option Expr)) :
                          MetaM (Option Expr) := do match es.find? e with
  | some e' => match e' with
    | none    => none                -- Remove `e`.
    | some e' => replaceMarked e' es -- Replace `e` with `e'` and process `e'`.
  | none    => match e with
    | app f e d       => match ← replaceMarked f es, ← replaceMarked e es with
       -- Replace `(APP f e)` with `(APP f' e')`.
      | some f', some e' => mkApp f' e'
       -- Replace `(APP f e)` with `e'`.
      | none   , some e' => e'
       -- Replace `(APP f e)` with `f'`.
      | some f', none    => f'
       -- Remove `(APP f e)`.
      | none   , none    => none
    | lam n t b d     => match ← replaceMarked b es with
      | none   => none
      | some b => mkLambda n d.binderInfo t b
    | forallE n t b d => match ← replaceMarked b es with
      | some b => mkForall n d.binderInfo t b
      | _      => none
    | letE n t v b d  => match ← replaceMarked t es,
                               ← replaceMarked v es,
                               ← replaceMarked b es with
      | some t, some v, some b => mkLet n t v b
      | _     , _     , _      => none
    | mdata m e s     => match ← replaceMarked e es with
      | none => none
      | some e => mkMData m e
    | proj s i e d    => match ← replaceMarked e es with
      | none => none
      | some e => mkProj s i e
    | e               => e

/-- Print an adjacency list of exprs using AST printer for `Expr`. -/
def List.toString (es : List (Expr × (Option Expr))) := s!"[" ++ String.intercalate ", " (es.map helper) ++ "]"
  where
    helper : Expr × (Option Expr) → String
    | (e, o) => s!"({exprToString e},{o.format.pretty})"

/-- Pre-processes `e` and returns the resulting expr. -/
def preprocessExpr (e : Expr) : MetaM Expr := do
  -- Print the `e` before the preprocessing step.
  trace[Smt.debug.transform] "Before: {exprToString e}"
  let mut es ← HashMap.empty
  -- Pass `e` through each pre-processing step to mark sub-exprs for removal or
  -- replacement. Note that each pass is passed the original expr `e` as an
  -- input. So, the order of the passes does not matter.
  for pass in passes do
    es := es ++ (← pass e)
  -- Print the exprs marked for removal/replacement.
  trace[Smt.debug.transform] "marked: {es.toList.toString}"
  -- Make the replacements and print the result.
  match ← replaceMarked e es with
    | none   => panic! "Error: Something went wrong..."
    | some e => trace[Smt.debug.transform] "After: {exprToString e}"; e
  where
    -- The passes to run through `e`.
    passes : List (Expr → MetaM (HashMap Expr (Option Expr))) :=
    [markTypeArgs,
     markInstArgs,
     markNatCons,
     markNatLiterals,
     markImps,
     markNatForalls]

/-- Converts a Lean expression into an SMT term. -/
partial def exprToTerm (e : Expr) : MetaM Term := do
  let e ← preprocessExpr e
  exprToTerm' e
  where
    exprToTerm' : Expr → MetaM Term
      | fvar id _ => do
        let n := (← Meta.getLocalDecl id).userName.toString
        Symbol n
      | const n .. => Symbol (match (knownConsts.find? n.toString) with
        | some n => n
        | none => n.toString)
      | sort l _ => Symbol
        (if l.isZero then "Bool" else "Sort " ++ ⟨Nat.toDigits 10 l.depth⟩)
      | e@(forallE n s b _) => do
        if e.isArrow then
          Meta.forallTelescope e fun ss s => do
            let ss ← ss.mapM Meta.inferType
            ss.foldrM (fun d c => do Arrow (← exprToTerm' d) (← c))
                      (← exprToTerm' s)
        else
          Forall n.toString (← exprToTerm' s) <|
            ← Meta.forallBoundedTelescope e (some 1) (fun _ b => exprToTerm' b)
      | app f t d         => do App (← exprToTerm' f) (← exprToTerm' t)
      | lit l d => Literal (match l with
        | Literal.natVal n => ⟨Nat.toDigits 10 n⟩
        | Literal.strVal s => s)
      | e => panic! "Unimplemented: " ++ exprToString e

end Smt.Transformer
