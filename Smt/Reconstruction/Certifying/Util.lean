import Lean

open Lean.Expr Lean

def andN : List Prop → Prop := λ l =>
  match l with
  | [] => True
  | h :: [] => h
  | h :: t  => h ∧ andN t
 
def orN : List Prop → Prop := λ l =>
  match l with
  | [] => False
  | h :: [] => h
  | h₁ :: h₂ :: t  => h₁ ∨ orN (h₂ :: t)
 
def notList : List Prop → List Prop :=
  List.map Not

def notExpr : Expr → Expr
| app (const `Not ..) e => e
| e => mkApp (mkConst `Not) e

def collectNOrNegArgs : Expr → Nat → List Expr
| app (app (const `Or ..) e) _,  1       => [notExpr e]
| app (app (const `Or ..) e1) e2, n + 1 => (notExpr e1) :: collectNOrNegArgs e2 n
| e, _ => [e]

def listExpr : List Expr → Expr → Expr
| [], ty => mkApp (const `List.nil [Level.zero]) ty
| e::es, ty => mkApp (mkApp (mkApp (const `List.cons [Level.zero]) ty) e) (listExpr es ty)

def collectPropsInOrChain : Expr → List Expr
| app (app (const `Or ..) e₁) e₂ => e₁ :: collectPropsInOrChain e₂
| e => [e]

def createOrChain : List Expr → Expr
| [] => mkConst `unreachable
| [h] => h
| h::t => app (app (mkConst `Or) h) $ createOrChain t

def getCongAssoc' : Nat → Name → Term
| 0,     n => mkIdent n
| i + 1, n => Syntax.mkApp (mkIdent `congOrLeft) #[getCongAssoc' i n]

def getCongAssoc : Nat → Name → List Term
| 0,     _ => []
| 1,     n => [getCongAssoc' 0 n]
| i + 2, n => (getCongAssoc' (i + 1) n) :: (getCongAssoc (i + 1) n)

def getLength (o : Expr) : Nat :=
  match o with
  | app (app (const `Or ..) _) e2 => 1 + getLength e2
  | _ => 1

def getNatLit? : Expr → Option Nat
| app (app _ (lit (Literal.natVal x))) _ => some x
| _ => none

open Lean.Elab.Tactic Lean.Meta in
def printGoal : TacticM Unit := do
  let currGoal ← getMainGoal
  let currGoalType ← MVarId.getType currGoal
  logInfo m!"......new goal: {← instantiateMVars currGoalType}"
