import Lean

namespace Smt.Preprocess

open Lean
open Lean.Expr
open Std

/-- Prints the given expression in AST format. -/
def exprToString : Expr → String
  | bvar id _         => "(BVAR " ++ ⟨Nat.toDigits 10 id⟩ ++ ")"
  | fvar id _         => "(FVAR " ++ id.name.toString ++ ")"
  | mvar id _         => "(MVAR " ++ id.name.toString ++ ")"
  | sort l _          => "(SORT " ++ l.format.pretty ++ ")"
  | const id _ _      => "(CONST " ++ id.toString ++ ")"
  | app f x _         => "(APP " ++ exprToString f ++ " " ++ exprToString x
                                 ++ ")"
  | lam id s e _      => "(LAM " ++ id.toString ++ " " ++ exprToString s
                                 ++ " " ++ exprToString e ++ ")"
  | forallE id s e _  => "(FORALL " ++ id.toString ++ " " ++ exprToString s
                                    ++ " " ++ exprToString e ++ ")"
  | letE id s e e' _  => "(LET " ++ id.toString ++ " " ++ exprToString s
                                 ++ " " ++ exprToString e ++ " "
                                 ++ exprToString e ++ ")"
  | lit l _           => "(LIT " ++ literalToString l ++ ")"
  | mdata m e _       => "(MDATA " ++ mdataToString m ++ " " ++ exprToString e
                                   ++ ")"
  | proj s i e _      => "(PROJ" ++ s.toString ++ " " ++ ⟨Nat.toDigits 10 i⟩
                                 ++ " " ++ exprToString e ++ ")"
  where
    literalToString : Literal → String
      | Literal.natVal v => ⟨Nat.toDigits 10 v⟩
      | Literal.strVal v => v
    mdataToString : Lean.MData → String
      | _ => ""

/-- Inserts entries in second hashmap into the first one. -/
def Std.HashMap.insertAll [BEq α] [Hashable α] :
  HashMap α β → HashMap α β → HashMap α β := HashMap.fold HashMap.insert

/-- Convenience `++` syntax for `Std.HashMap.insertAll`. -/
instance [BEq α] [Hashable α] : Append (HashMap α β) := ⟨Std.HashMap.insertAll⟩

/-- Traverses `e` and marks type arguments in apps for removal. For example,
    given `(App (App (App Eq Prop) p) q)`, this method should mark `Prop` for
    removal and the resulting expr will be `(App (App Eq p) q)`. -/
partial def markTypeArgs (e : Expr) : MetaM (HashMap Expr (Option Expr)) :=
  do match e with
  | app f e d       => if ← hasValidSort e then
                         (← markTypeArgs f) ++ (← markTypeArgs e)
                       else (← markTypeArgs f).insert e none
  | lam n t b d     => (← markTypeArgs t)
    ++ (← Meta.withLocalDecl n d.binderInfo t (fun b => markTypeArgs b))
  | forallE n t b d => (← markTypeArgs t)
    ++ (← Meta.withLocalDecl n d.binderInfo t (fun b => markTypeArgs b))
  | letE n t v b d  => (← markTypeArgs t) ++ (← markTypeArgs v)
   ++ (← Meta.withLetDecl n t v (fun b => markTypeArgs b))
  | mdata m e s     => markTypeArgs e
  | proj s i e d    => markTypeArgs e
  | e               => HashMap.empty
  where
    -- Returns the whether or not we should add `e` to the argument list
    -- (i.e., skip implicit sort arguments).
    hasValidSort (e : Expr) : MetaM Bool := do
      let type ← Lean.Meta.inferType e
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
  | lam n t b d     => (← markInstArgs t)
    ++ (← Meta.withLocalDecl n d.binderInfo t (fun b => markInstArgs b))
  | forallE n t b d => (← markInstArgs t)
    ++ (← Meta.withLocalDecl n d.binderInfo t (fun b => markInstArgs b))
  | letE n t v b d  => (← markInstArgs t) ++ (← markInstArgs v)
    ++ (← Meta.withLetDecl n t v (fun b => markInstArgs b))
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
  | lam n t b d              => (← markNatCons t)
    ++ (← Meta.withLocalDecl n d.binderInfo t (fun b => markNatCons b))
  | forallE n t b d          => (← markNatCons t)
    ++ (← Meta.withLocalDecl n d.binderInfo t (fun b => markNatCons b))
  | letE n t v b d           => (← markNatCons t)
    ++ (← markNatCons v)
    ++ (← Meta.withLetDecl n t v (fun b => markNatCons b))
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
  | lam n t b d     => (← markNatLiterals t) ++
    (← Meta.withLocalDecl n d.binderInfo t (fun b => markNatLiterals b))
  | forallE n t b d => (← markNatLiterals t)
    ++ (← Meta.withLocalDecl n d.binderInfo t (fun b => markNatLiterals b))
  | letE n t v b d  => (← markNatLiterals t) ++ (← markNatLiterals v)
    ++ (← Meta.withLetDecl n t v (fun b => markNatLiterals b))
  | mdata m e s     => markNatLiterals e
  | proj s i e d    => markNatLiterals e
  | e               => HashMap.empty
  where
    toLiteral : Expr → Option Expr
      | app (app (const n ..) ..) l .. =>
        if n.toString = "OfNat.ofNat" then l else e
      | e                              => none

/-- Traverses `e` and marks arrows for replacement with `Imp`. For example,
    given `(FORALL _ p q)`, this method should mark the given expr for
    replacement with `(Imp p q)`. The replacement is done at this stage because
    `e` is a well-typed Lean term. So, we can ask Lean to infer the type of `p`,
    which is not possible after the pre-processing step. -/
partial def markImps (e : Expr) : MetaM (HashMap Expr (Option Expr)) :=
  do match e with
  | app f e d           => (← markImps f) ++ (← markImps e)
  | lam n t b d         => (← markImps t) ++ (← Meta.withLocalDecl n d.binderInfo t (fun b => markImps b))
  | e@(forallE n t b d) =>
    if e.isArrow && (← Meta.inferType t).isProp then
      (← markImps b).insert e (mkApp2 imp t b)
    else (← markImps t)
      ++ (← Meta.withLocalDecl n d.binderInfo t (fun b => markImps b))
  | letE n t v b d      => (← markImps t) ++ (← markImps v)
    ++ (← Meta.withLetDecl n t v (fun b => markImps b))
  | mdata m e s         => markImps e
  | proj s i e d        => markImps e
  | e                   => HashMap.empty
  where
    imp := mkConst (Name.mkSimple "Imp")

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
  | some e' =>
    match e' with
    | none    => none                -- Remove `e`.
    | some e' => replaceMarked e' es -- Replace `e` with `e'` and process `e'`.
  | none   => do match e with
    | app f e d       => match ← replaceMarked f es, ← replaceMarked e es with
       -- Replace `(APP f e)` with `some (APP f' e')`.
      | some f', some e' => mkApp f' e'
       -- Replace `(APP f e)` with `some e'`.
      | none  , some e'  => e'
       -- Replace `(APP f e)` with `some f'`.
      | some f', none    => f'
       -- Replace `(APP f e)` with `none`.
      | none  , none     => none
    | lam n t b d     =>
      match ← replaceMarked t es,
            ← Meta.withLocalDecl n d.binderInfo t fun _ => replaceMarked b es
      with
      | some t, some b => mkLambda n d.binderInfo t b
      | _     , _      => none
    | forallE n t b d =>
      match ← replaceMarked t es,
            ← Meta.withLocalDecl n d.binderInfo t fun _ => replaceMarked b es
      with
      | some t, some b => mkForall n d.binderInfo t b
      | _     , _      => none
    | letE n t v b d  =>
      match ← replaceMarked t es,
            ← replaceMarked v es,
            ← Meta.withLetDecl n t v fun _ => replaceMarked b es
      with
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
  IO.println s!"Before: {exprToString e}"
  let mut es ← HashMap.empty
  -- Pass `e` through each pre-processing step to mark sub-exprs for removal or
  -- replacement. Note that each pass is passed the original expr `e` as an
  -- input. So, the order of the passes does not matter.
  for pass in passes do
    es := es ++ (← pass e)
  -- Print the exprs marked for removal/replacement.
  IO.println s!"marked: {es.toList.toString}"
  -- Make the replacements and print the result.
  match ← replaceMarked e es with
    | none   => panic! "Error: Something went wrong..."
    | some e => IO.println s!"After: {exprToString e}"; e
  where
    -- The passes to run through `e`.
    passes : List (Expr → MetaM (HashMap Expr (Option Expr))) :=
    [markTypeArgs,
     markInstArgs,
     markNatCons,
     markNatLiterals,
     markImps]

end Smt.Preprocess
