import Lean
import Smt.Preprocess
import Smt.Term

namespace Smt
namespace Util

open Lean
open Lean.Expr
open Smt.Term

/-- Returns all free variables in the given expression. -/
def getFVars : Expr → List Expr
  | forallE _ d b _ => getFVars d ++ getFVars b
  | lam _ d b _     => getFVars d ++ getFVars b
  | letE _ t v b _  => getFVars t ++ getFVars v ++ getFVars b
  | app f a _       => getFVars f ++ getFVars a
  | mdata _ b _     => getFVars b
  | proj _ _ b _    => getFVars b
  | fvar id d       => [fvar id d]
  | _               => []

/-- Returns all free variables in the type of the given expression. -/
def getTypeFVars (e : Expr) : MetaM (List Expr) := do getFVars (← Meta.inferType e)

/-- Returns all free variables in the type of the given expressions. -/
def getAllTypeFVars (es : List Expr) : MetaM (List Expr) := do
  (← es.foldlM (fun a e => return (← getTypeFVars e) ++ a) []) ++ es

partial def fixedPoint [BEq α] (f : List α → MetaM (List α)) (x : List α) : MetaM (List α) := do
  let x' := (← f x).eraseDups
  if x'.length == x.length then x else fixedPoint f x'

/-- Converts the given constant into the corresponding SMT constant/function symbol. -/
def knownSymbols : Std.HashMap String String :=
  List.foldr (fun (k, v) m => m.insert k v) Std.HashMap.empty
  [
    ("And", "and"),
    ("Eq" , "="),
    ("Ne", "distinct"),
    ("False", "false"),
    ("Iff", "="),
    ("Not", "not"),
    ("Or" , "or"),
    ("Imp", "=>"),
    ("True", "true"),
    ("Bool.true", "true"),
    ("Bool.false", "false"),
    ("BEq.beq", "="),
    ("Nat", "Int"),
    ("HAdd.hAdd", "+"),
    ("HSub.hSub", "-"),
    ("HMul.hMul", "*"),
    ("HDiv.hDiv", "/"),
    ("HMod.hMod", "mod"),
    ("Nat.min", "min"),
    ("Nat.zero", "0")
  ]

def getUnkownConsts : Expr → List Expr
  | app f e d       => getUnkownConsts f ++ getUnkownConsts e
  | lam n t b d     => getUnkownConsts t ++ getUnkownConsts b
  | forallE n t b d => getUnkownConsts t ++ getUnkownConsts b
  | letE n t v b d  => getUnkownConsts t ++ getUnkownConsts v ++ getUnkownConsts b
  | mdata m e s     => getUnkownConsts e
  | proj s i e d    => getUnkownConsts e
  | e@(const n l d) => if knownSymbols.contains n.toString then [] else [e]
  | e               => []

/-- Returns the function name and arguments of the given application. -/
def appList : Lean.Expr → Lean.Expr × List Lean.Expr
  | app (bvar f d) e ..   => ((bvar f d), [e])
  | app (fvar f d) e ..   => ((fvar f d), [e])
  | app f@(const ..) e .. => (f, [e])
  | app f e ..            => let (f, ts) := appList f; (f, ts ++ [e])
  | _                     => panic! "Input expression must be an application!"

/-- Converts a Lean expression into an SMT term. -/
partial def exprToTerm' : Lean.Expr → Lean.MetaM Term
  | fvar id d => do
    let n := (← Lean.Meta.getLocalDecl id).userName.toString
    Symbol n
  | const n _ _ => Symbol (match (knownSymbols.find? n.toString) with | some n => n | none => n.toString)
  | sort l _ => Symbol (if l.isZero then "Bool" else "Sort " ++ ⟨Nat.toDigits 10 l.depth⟩)
  | e@(forallE n s b _) => do
    if e.isArrow then
      Lean.Meta.forallTelescope e fun ss s => do
        let ss ← ss.mapM Lean.Meta.inferType
        ss.foldrM (fun d c => do Arrow (← exprToTerm' d) (← c)) (← exprToTerm' s)
    else
      Forall n.toString (← exprToTerm' s) <|
        ← Lean.Meta.forallBoundedTelescope e (some 1) (fun _ b => exprToTerm' b)
  | app f t d         => do App (← exprToTerm' f) (← exprToTerm' t)
  | lit l d => Term.Literal (match l with | Literal.natVal n => ⟨Nat.toDigits 10 n⟩ | Literal.strVal s => s)
  | _ => panic! "Unimplemented"

/-- Converts a Lean expression into an SMT term. -/
partial def exprToTerm (e : Lean.Expr) : Lean.MetaM Term := do
  let e ← Preprocess.preprocessExpr e
  exprToTerm' e

end Util
end Smt
