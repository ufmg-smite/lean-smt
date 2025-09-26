import Smt.Preprocess.Iff

syntax (name := elimIff) "elim_iff " "[" term,* "]" : tactic

open Lean.Elab Tactic in
@[tactic elimIff] def evalReconstruct : Tactic
  | `(tactic| elim_iff [$hs,*]) => withMainContext do
    let mv ← getMainGoal
    let hs ← hs.getElems.mapM (Term.elabTerm · none)
    Lean.logInfo m!"Before: {hs}"
    let ⟨_, hs, mv⟩ ← Smt.Preprocess.elimIff mv hs
    mv.withContext (Lean.logInfo m!"After: {hs}")
    replaceMainGoal [mv]
  | _ => throwUnsupportedSyntax

def t (p : Prop) : p ↔ p := by simp

example (p q r : Prop) (ht : True) (hpqr : (p ↔ q) ∧ (q ↔ r)) (ht' : True) : p ↔ r := by
  elim_iff [hpqr, ht, ht', t]
  simp_all
