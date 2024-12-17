/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

namespace Smt.Reconstruct

open Lean Expr Elab.Tactic Meta

def andN : List Prop → Prop
| [] => True
| h :: [] => h
| h :: t  => h ∧ andN t

def orN : List Prop → Prop
| [] => False
| h :: [] => h
| h₁ :: h₂ :: t  => h₁ ∨ orN (h₂ :: t)

def andN' (ps : List Prop) (q : Prop) : Prop := match ps with
| [] => q
| p :: ps => p ∧ andN' ps q

def impliesN (ps : List Prop) (q : Prop) : Prop := match ps with
  | [] => q
  | p :: ps => p → impliesN ps q

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

def collectPropsInOrChain : Expr → MetaM (List Expr)
| app (app (const ``Or ..) e₁) e₂ => (e₁ :: ·) <$> collectPropsInOrChain e₂
| e => pure [e]

def createOrChain : List Expr → MetaM Expr
| []   => throwError "createOrChain with empty list"
| [h]  => pure h
| h::t => app (app (mkConst ``Or) h) <$> createOrChain t

def foldAndExpr : List Expr → MetaM Expr
| []   => throwError "[foldAndExpr]: empty list"
| [h]  => pure h
| h::t => app (app (mkConst ``And) h) <$> foldAndExpr t

-- fold the l-th suffix into one expr
def collectPropsInOrChain' : Nat → Expr → MetaM (List Expr)
| l, e => do
  let li ← collectPropsInOrChain e
  let pref := List.take l li
  let suff := List.drop l li
  let suffE ←
    match suff with
    | [] => pure []
    | _  => pure [← createOrChain suff]
  pure (pref ++ suffE)

def collectPropsInAndChain : Expr → MetaM (List Expr)
| app (app (const ``And ..) e₁) e₂ => (e₁ :: ·) <$> collectPropsInAndChain e₂
| e => pure [e]

-- fold the l-th suffix into one expr
def collectPropsInAndChain' : Nat → Expr → MetaM (List Expr)
| l, e => do
  let li ← collectPropsInAndChain e
  let pref := List.take l li
  let suff := List.drop l li
  let suffE ←
    match suff with
    | [] => pure []
    | _  => pure [← foldAndExpr suff]
  pure (pref ++ suffE)

def pull! [Inhabited α] (i j : Nat) (xs : List α) : List α :=
  List.flatten
    [ xs.take i
    , [xs.get! j]
    , List.drop i (xs.eraseIdx j)
    ]

-- 0-based
-- inclusive on both sides
def subList (i j : Nat) (xs : List α) : List α :=
  List.take (j + 1 - i) (xs.drop i)

def permutateList [Inhabited α] : List α → List Nat → List α :=
  λ xs => List.foldr (λ i => (· :: ·) (List.get! xs i)) []

def findIndex? [BEq α] : List α → α → Option Nat
| [], _ => none
| x::xs, a =>
  if a == x then
    some 0
  else (· + 1) <$> findIndex? xs a

def getIndex : Expr → Expr → MetaM (Option Nat)
| t, e => do
  let props ← collectPropsInOrChain e
  pure $ findIndex? props t

-- this one considers a suffIdx
def getIndex' : Expr → Expr → Nat → MetaM (Option Nat)
| t, e, suffIdx => do
  let props ← collectPropsInOrChain' suffIdx e
  pure $ findIndex? props t

def getFirstBinderName : Expr → MetaM Name
| app e _ => getFirstBinderName e
| const nm .. => pure nm
| _ => throwError "[getFirstBinderName]: unknown expression"

def getLength : Expr → (i : Option Nat := none) → MetaM Nat
| e, some i => do
  let li ← collectPropsInOrChain' i e
  pure $ List.length li
| e, none => do
  let li ← collectPropsInOrChain e
  pure $ List.length li

def getLengthAnd : Expr → Nat
| app (app (const ``And ..) _) e2 => 1 + getLengthAnd e2
| _ => 1

def getNatLit? : Expr → Option Nat
| app (app _ (lit (Literal.natVal x))) _ => some x
| _ => none

def getIthExpr? : Nat → Expr → MetaM (Option Expr) :=
  λ i e => do pure $ List.get? (← collectPropsInOrChain e) i

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

def getOp : Expr → MetaM Name
  | app (Expr.const ``Not ..) e' => getOp e'
  | app (app (app (app (app (Expr.const nm ..) ..) ..) ..) ..) .. => pure nm
  | app (app (app (app (Expr.const nm ..) ..) ..) ..) .. => pure nm
  | app (app (app (Expr.const nm ..) ..) ..) .. => pure nm
  | _ => throwError "[getOp] invalid parameter"

-- Still in process of development
partial def expandLet : Expr → MetaM Expr
| fvar fid => do
    let lctx ← getLCtx
    match lctx.find? fid with
    | some (.ldecl _ _ userName _ value _ _) =>
      match userName with
      | .str _ ⟨userNameStr⟩ =>
        let userNamePref: String := ⟨List.take 3 userNameStr⟩
        if userNamePref = "let" then expandLet value else pure (fvar fid)
      | _ => pure (fvar fid)
    | _ => pure (fvar fid)
| app f x => do pure (app (← expandLet f) (← expandLet x))
| lam bn bt body bi => do pure (lam bn (← expandLet bt) (← expandLet body) bi)
| forallE bn bt body bi => do
    pure (lam bn (← expandLet bt) (← expandLet body) bi)
| letE nm tp val bd nDep => do
    pure (letE nm (← expandLet tp) (← expandLet val) (← expandLet bd) nDep)
| e => pure e


syntax (name := printType) "printType" term : tactic

@[tactic printType] def evalPrintType : Tactic := fun stx =>
  withMainContext do
    let e ← elabTerm stx[1] none
    let t ← inferType e
    logInfo m!"t = {t}"
    let e' ← expandLet e
    logInfo m!"e' = {e'}"
    let t ← inferType e'
    let t' ← expandLet t
    logInfo m!"t' = {t'}"

end Smt.Reconstruct
