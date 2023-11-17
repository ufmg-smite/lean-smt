import Lean
import Mathlib.Tactic.LibrarySearch

open Lean Elab Tactic Meta

namespace Smt.Reconstruction.Certifying

syntax (name := smtCongr) "smtCongr"  ("[" term,* "]")? : tactic

def termToSyntax : Term → TacticM Syntax := fun t => pure t

def parseSmtCongr : Syntax → TacticM (List Expr)
  | `(tactic| smtCongr  [ $[$hs],* ]) => withMainContext do
    let hs' : List Syntax ← hs.toList.mapM termToSyntax
    hs'.mapM (elabTerm · none)
  | _ => throwError "[smtCongr]: invalid Syntax"

def rewriteHyp (hyp : Expr) (mvar : MVarId) : MetaM MVarId :=
  mvar.withContext do
    let type ← mvar.getType
    let r ← mvar.rewrite type hyp
    let mvar' ← mvar.replaceTargetEq r.eNew r.eqProof
    pure mvar'

def smtCongrCore (es : List Expr) (mvar: MVarId) : MetaM Unit := do
  let mvar' ← es.foldrM rewriteHyp mvar
  mvar'.refl

@[tactic smtCongr] def evalSmtCongr : Tactic := fun stx => do
  let es ← parseSmtCongr stx
  let mvar ← getMainGoal
  smtCongrCore es mvar

example (a b c d : Int) : a = b → c = d → a + c = b + d := by
  intros h₁ h₂
  smtCongr [h₁, h₂]

end Smt.Reconstruction.Certifying
