import Lean

open Lean Expr Elab.Tactic Meta

def andN : List Prop → Prop
| [] => True
| h :: [] => h
| h :: t  => h ∧ andN t
 
def orN : List Prop → Prop
| [] => False
| h :: [] => h
| h₁ :: h₂ :: t  => h₁ ∨ orN (h₂ :: t)
 
def notList : List Prop → List Prop := List.map Not

def notExpr : Expr → Expr
| app (const `Not ..) e => e
| e => mkApp (mkConst `Not) e

def collectOrNNegArgs : Expr → Nat → List Expr
| app (app (const `Or ..) e) _,  1      => [notExpr e]
| app (app (const `Or ..) e1) e2, n + 1 =>
  notExpr e1 :: collectOrNNegArgs e2 n
| e, _ => [e]

-- Creates the expr corresponding to the list of values passed
-- The second argument is the type of the elements of the list
def listExpr : List Expr → Expr → Expr
| [], ty    => mkApp (const `List.nil [Level.zero]) ty
| e::es, ty =>
  mkApp (mkApp (mkApp (const `List.cons [Level.zero]) ty) e) (listExpr es ty)

def collectPropsInOrChain : Expr → List Expr
| app (app (const `Or ..) e₁) e₂ => e₁ :: collectPropsInOrChain e₂
| e => [e]

def createOrChain : List Expr → Expr
| []   => panic! "createOrChain with empty list"
| [h]  => h
| h::t => app (app (mkConst `Or) h) $ createOrChain t

def getIndex : Expr → Expr → Option Nat
| t, app (app (const `Or ..) e1) e2 =>
    if e1 == t then some 0
    else (. + 1) <$> getIndex t e2
| t, e => if e == t then some 0
          else none

def getCongAssoc' : Nat → Name → Term
| 0,     n => mkIdent n
| i + 1, n =>
  Syntax.mkApp (mkIdent `congOrLeft) #[getCongAssoc' i n]

-- tactics for parenthesizing the prefix of an or-chain
def getCongAssoc : Nat → Name → List Term
| 0,     _ => []
| 1,     n => [getCongAssoc' 0 n]
| i + 2, n => (getCongAssoc' (i + 1) n) :: (getCongAssoc (i + 1) n)

def getLength : Expr → Nat
| app (app (const `Or ..) _) e2 => 1 + getLength e2
| _ => 1

def getNatLit? : Expr → Option Nat
| app (app _ (lit (Literal.natVal x))) _ => some x
| _ => none

def getIthExpr? : Nat → Expr → Option Expr := λ i e =>
  List.get? (collectPropsInOrChain e) i

def stxToNat (h : Term) : TacticM Nat := do
  let expr ← elabTerm h.raw none
  match getNatLit? expr with
  | some i => pure i
  | none   => throwError "getNatLit? failed"

def getTypeFromName (name : Name) : TacticM Expr :=
  withMainContext do
    let ctx ← getLCtx
    inferType (ctx.findFromUserName? name).get!.toExpr

def printGoal : TacticM Unit := do
  let currGoal ← getMainGoal
  let currGoalType ← getMVarType currGoal
  logInfo m!"......new goal: {← instantiateMVars currGoalType}"

