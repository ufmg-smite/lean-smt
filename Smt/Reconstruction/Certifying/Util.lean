/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

namespace Smt.Reconstruction.Certifying.Util

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
| app (const ``Not ..) e => e
| e => mkApp (mkConst ``Not) e

def collectOrNNegArgs : Expr → Nat → List Expr
| app (app (const ``Or ..) e) _,  1      => [notExpr e]
| app (app (const ``Or ..) e1) e2, n + 1 =>
  notExpr e1 :: collectOrNNegArgs e2 n
| e, _ => [e]

-- Creates the expr corresponding to the list of values passed
-- The second argument is the type of the elements of the list
def listExpr : List Expr → Expr → Expr
| [], ty    => mkApp (const ``List.nil [Level.zero]) ty
| e::es, ty =>
  mkApp (mkApp (mkApp (const ``List.cons [Level.zero]) ty) e) (listExpr es ty)

def collectPropsInOrChain : Expr → List Expr
| app (app (const ``Or ..) e₁) e₂ => e₁ :: collectPropsInOrChain e₂
| e => [e]

def createOrChain : List Expr → Expr
| []   => panic! "createOrChain with empty list"
| [h]  => h
| h::t => app (app (mkConst ``Or) h) $ createOrChain t

def foldAndExpr : List Expr → Expr
| [] => panic! "[foldAndExpr]: empty list"
| [h] => h
| h::t => app (app (mkConst ``And) h) $ foldAndExpr t

-- fold the l-th suffix into one expr
def collectPropsInOrChain' : Nat → Expr → List Expr
| l, e =>
  let li := collectPropsInOrChain e
  let pref := List.take l li
  let suff := List.drop l li
  let suffE := createOrChain suff
  pref ++ [suffE]

def pull! [Inhabited α] (i j : Nat) (xs : List α) : List α :=
  List.join
    [ xs.take i
    , [xs.get! j]
    , List.drop i (xs.eraseIdx j)
    ]

-- 0-based
-- inclusive on both sides
def subList (i j : Nat) (xs : List α) : List α :=
  List.take (j + 1 - i) (xs.drop i)


def getIndexList [BEq α] : α → List α → Option Nat
| _, [] => none
| a, (x::xs) =>
  if a == x then some 0
  else (· + 1) <$> getIndexList a xs

def permutateList [Inhabited α] : List α → List Nat → List α :=
  λ xs => List.foldr (λ i => (· :: ·) (List.get! xs i)) []

def getIndex : Expr → Expr → Option Nat
| t, app (app (const ``Or ..) e1) e2 =>
    if e1 == t then some 0
    else (. + 1) <$> getIndex t e2
| t, e => if e == t then some 0
          else none

def getFirstBinderName : Expr → Name
| app e _ => getFirstBinderName e
| const nm .. => nm
| _ => panic! "[getFirstBinderName]: unknown expression"

def getLength : Expr → (i : Option Nat := none) → Nat
| e, some i =>
  let li := collectPropsInOrChain' i e
  List.length li
| e, none =>
  let li := collectPropsInOrChain e
  List.length li

def getLengthAnd : Expr → Nat
| app (app (const ``And ..) _) e2 => 1 + getLengthAnd e2
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

def mkLam (type body : Expr) : Expr :=
  lam Name.anonymous type body BinderInfo.default

def mkForall' (t b : Expr) : Expr :=
  forallE Name.anonymous t b BinderInfo.default

partial def expandType' (mvar : MVarId) : Expr → MetaM Expr := fun e =>
  match e with
  | fvar fid => mvar.withContext do
    let lctx ← getLCtx
    match lctx.find? fid with
    | some ldcl => expandType' mvar ldcl.value
    | none      => pure e
  | _ => pure e

def expandTypesInOrChain' (mvar : MVarId) : Expr → MetaM Expr := fun e =>
  do let es := collectPropsInOrChain e
     let esExpanded ← List.mapM (expandType' mvar) es
     let e' := createOrChain esExpanded
     pure e'

partial def expandType : Expr → TacticM Expr := fun e =>
  match e with
  | fvar fid => withMainContext do
    let lctx ← getLCtx
    match lctx.find? fid with
    | some ldcl => expandType ldcl.value
    | none      => pure e
  | _ => pure e

def expandTypesInOrChain : Expr → TacticM Expr := fun e => do
  let es         := collectPropsInOrChain e
  let esExpanded ← List.mapM expandType es
  let e'         := createOrChain esExpanded
  pure e'

def printGoal : TacticM Unit := do
  let currGoal ← getMainGoal
  let currGoalType ← MVarId.getType currGoal
  logInfo m!"......new goal: {← instantiateMVars currGoalType}"

syntax (name := cmdElabTerm) "#elab " term : command
open Lean.Elab Lean.Elab.Command in
@[command_elab cmdElabTerm] def evalCmdElabTerm : CommandElab
  | `(#elab%$tk $term) => withoutModifyingEnv $ runTermElabM fun _ => do
    let e ← Term.elabTerm term none
    unless e.isSyntheticSorry do
      logInfoAt tk m!"{e} ::: {repr e}"
  | _ => throwUnsupportedSyntax

end Smt.Reconstruction.Certifying.Util
