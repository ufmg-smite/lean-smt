import Lean
import Smt.Term

namespace Smt
namespace Util

open Lean
open Lean.Expr
open Smt.Term

/-- Context data-structure for `exprToTerm` function. -/
structure Context where
  bvars : List (Name × Expr)                   -- The current list of bound variables (and their type).
  fvars : Std.HashMap Lean.Expr Lean.LocalDecl -- A mapping from for free variables to their infos.

/-- Converts the given constant into the corresponding SMT constant/function symbol. -/
def toSmtFun : String → Option String
  | "And" => "and"
  | "Eq"  => "="
  | "False" => "false"
  | "Iff" => "="
  | "Not" => "not"
  | "Or"  => "or"
  | "True" => "true"
  | _     => none

/-- Returns the function name and arguments of the given application -/
def appList : Lean.Expr → Lean.Elab.Tactic.TacticM (Lean.Expr × List Lean.Expr)
  | app (bvar f d) e ..     => do
    if (← hasValidSort e) then ((bvar f d), [e]) else ((bvar f d), [])
  | app (fvar f d) e ..     => do
    if (← hasValidSort e) then ((fvar f d), [e]) else ((fvar f d), [])
  | app (const f ls d) e .. => do
    if (← hasValidSort e) then ((const f ls d), [e]) else ((const f ls d), [])
  | app f e ..              => do
    let (f, ts) ← appList f
    if (← hasValidSort e) then (f, ts ++ [e]) else (f, ts)
  | _                       => panic! "Input expression must be an application!"
  where
    -- Returns the whether or not we should add `e` to the argument list (i.e., skip implicit sort arguments )
    hasValidSort (e : Expr) : Lean.Elab.Tactic.TacticM Bool := do
      let type ← Lean.Meta.inferType e
      match type with
      | sort l .. => l.isZero
      | _         => true

/-- Converts a Lean expression into an SMT term. -/
partial def exprToTerm' (ctx : Context) : Lean.Expr → Lean.Elab.Tactic.TacticM Term
  | bvar n _ => Var (List.get! n ctx.bvars).fst.toString
  | fvar n d => Const (ctx.fvars.find! (fvar n d)).userName.toString
  | const n _ _ => Const (match (toSmtFun n.toString) with | some n => n | none => n.toString)
  | sort l _ => Const (if l.isZero then "Bool" else "Sort " ++ ⟨Nat.toDigits 10 l.depth⟩)
  | forallE n s b _ => let ctx' : Context := ⟨(n, s) :: ctx.bvars, ctx.fvars⟩
  do
    if s.isBVar && (List.get! s.bvarIdx! ctx.bvars).snd.isProp then
      App "=>" [(← exprToTerm' ctx s), (← exprToTerm' ctx' b)]
    else if (← Lean.Meta.inferType s).isProp then
      App "=>" [(← exprToTerm' ctx s), (← exprToTerm' ctx' b)]
    else
      Forall n.toString (← exprToTerm' ctx s) (← exprToTerm' ctx' b)
  | app f t d         => do
    let (f, ts) ← appList (app f t d)
    App (← exprToTerm' ctx f).toString (← ts.mapM (exprToTerm' ctx))
  | _ => panic! "Unimplemented"

/-- Prints the given expression in AST format. -/
def exprToString : Lean.Expr → String
  | bvar id _         => "(BVAR " ++ ⟨Nat.toDigits 10 id⟩ ++ ")"
  | fvar id _         => "(FVAR " ++ id.toString ++ ")"
  | mvar id _         => "(MVAR " ++ id.toString ++ ")"
  | sort l _          => "(SORT " ++ l.format.pretty ++ ")"
  | const id _ _      => "(CONST " ++ id.toString ++ ")"
  | app f x _         => "(APP " ++ exprToString f ++ " " ++ exprToString x ++ ")"
  | lam id s e _      => "(LAM " ++ id.toString ++ " " ++ exprToString s ++ " " ++ exprToString e ++ ")"
  | forallE id s e _  => "(FORALL " ++ id.toString ++ " " ++ exprToString s ++ " " ++ exprToString e ++ ")"
  | letE id s e e' _  => "(LET " ++ id.toString ++ " " ++ exprToString s ++ " " ++ exprToString e ++ " " ++ exprToString e ++ ")"
  | lit l _           => "(LITERAL " ++ literalToString l ++ ")"
  | mdata m e _       => "(MDATA " ++ mdataToString m ++ " " ++ exprToString e ++ ")"
  | proj s i e _      => "(PROJ" ++ s.toString ++ " " ++ ⟨Nat.toDigits 10 i⟩ ++ " " ++ exprToString e ++ ")"
  where
    literalToString : Lean.Literal → String
      | Lean.Literal.natVal v => ⟨Nat.toDigits 10 v⟩
      | Lean.Literal.strVal v => v
    mdataToString : Lean.MData → String
      | _ => ""

/-- Returns all free variables in the given expression. -/
def getFVars : Lean.Expr → List Lean.Expr
  | forallE _ d b _ => getFVars d ++ getFVars b
  | lam _ d b _     => getFVars d ++ getFVars b
  | letE _ t v b _  => getFVars t ++ getFVars v ++ getFVars b
  | app f a _       => getFVars f ++ getFVars a
  | mdata _ b _     => getFVars b
  | proj _ _ b _    => getFVars b
  | fvar id d       => [fvar id d]
  | _               => []

end Util
end Smt
