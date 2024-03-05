/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct.Quant.Lemmas
import Smt.Reconstruct.Reconstruct

/-- Takes an array `xs` of free variables or metavariables and a term `e` that may contain those variables, and abstracts and binds them as existential quantifiers.

- if `usedOnly = true` then only variables that the expression body depends on will appear.
- if `usedLetOnly = true` same as `usedOnly` except for let-bound variables. (That is, local constants which have been assigned a value.)
 -/
def Lean.Meta.mkExistsFVars (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) (usedLetOnly : Bool := true) (binderInfoForMVars := BinderInfo.implicit) : MetaM Expr := do
  let e ← if xs.isEmpty then return e else liftMkBindingM <| MetavarContext.mkLambda xs e usedOnly usedLetOnly binderInfoForMVars
  addExists e xs.size
where
  addExists : Expr → Nat → MetaM Expr
    | .lam n t b i, m + 1 => do
      let b ← addExists b m
      mkAppM ``Exists #[.lam n t b i]
    | e, _ => pure e

namespace Smt.Reconstruct.Quant

open Lean Qq

@[smt_term_reconstruct] def reconstructQuant : TermReconstructor := fun t => do match t.getKind with
  | .FORALL =>
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    withNewTermCache $ Meta.withLocalDeclsD xs fun xs => do
      let b ← reconstructTerm t[1]!
      Meta.mkForallFVars xs b
  | .EXISTS =>
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    withNewTermCache $ Meta.withLocalDeclsD xs fun xs => do
      let b ← reconstructTerm t[1]!
      Meta.mkExistsFVars xs b
  | .LAMBDA =>
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    withNewTermCache $ Meta.withLocalDeclsD xs fun xs => do
      let b ← reconstructTerm t[1]!
      Meta.mkLambdaFVars xs b
  | .HO_APPLY =>
    return (← reconstructTerm t[0]!).app (← reconstructTerm t[1]!)
  | .SKOLEM_FUN => match t.getSkolemId with
    | .QUANTIFIERS_SKOLEMIZE =>
      let q := t.getSkolemArguments[0]!
      let n := t.getSkolemArguments[1]!.getIntegerValue.toNat
      let es ← if q.getKind == .EXISTS then reconstructExistsSkolems q n else reconstructForallSkolems q n
      return es[n]!
    | _ => return none
  | _ => return none
where
  reconstructForallSkolems (q : cvc5.Term) (n : Nat) : ReconstructM (Array Expr) := do
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    let mut es := #[]
    for x in q[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    let F := q[0]![1]!
    for i in [0:n + 1] do
      let α : Q(Type) ← reconstructSort q[0]![0]![i]!.getSort
      let h : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
      let e ← withNewTermCache $ Meta.withLocalDeclsD xs fun xs => do
        let F ← reconstructTerm F
        let F' := F.replaceFVars xs[0:i] es
        let ysF' ← Meta.mkExistsFVars xs[i + 1:n + 1] F'
        let xysF' : Q($α → Prop) ← Meta.mkLambdaFVars #[xs[i]!] (.app q(Not) ysF')
        return q(@Classical.epsilon $α $h $xysF')
      es := es.push e
    return es
  reconstructExistsSkolems (q : cvc5.Term) (n : Nat) : ReconstructM (Array Expr) := do
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    let mut es := #[]
    for x in q[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    let F := q[1]!
    for i in [0:n + 1] do
      let α : Q(Type) ← reconstructSort q[0]![i]!.getSort
      let h : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
      let e ← withNewTermCache $ Meta.withLocalDeclsD xs fun xs => do
        let F ← reconstructTerm F
        let F' := F.replaceFVars xs[0:i] es
        let ysF' ← Meta.mkExistsFVars xs[i + 1:n + 1] F'
        let xysF' : Q($α → Prop) ← Meta.mkLambdaFVars #[xs[i]!] ysF'
        return q(@Classical.epsilon $α $h $xysF')
      es := es.push e
    return es
  getVariableName (t : cvc5.Term) : Name :=
    if t.hasSymbol then t.getSymbol else Name.num `x t.getId
  withNewTermCache {α} (k : ReconstructM α) : ReconstructM α := do
    let state ← get
    let r ← k
    set { ← get with termCache := state.termCache }
    return r

@[smt_proof_reconstruct] def reconstructQuantProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .CONG =>
    let k := pf.getResult[0]!.getKind
    -- This rule needs more care for closures.
    if k == .FORALL then
      reconstructForallCong pf
    else
      return none
  | .BETA_REDUCE =>
    let α : Q(Type) ← reconstructSort pf.getResult[0]!.getSort
    let t  : Q($α) ← reconstructTerm pf.getResult[0]!
    let t' : Q($α) ← reconstructTerm pf.getResult[1]!
    addThm q($t = $t') q(Eq.refl $t)
  | .SKOLEMIZE => reconstructSkolemize pf
  | .INSTANTIATE =>
    let xsF  : Q(Prop) ← reconstructProof pf.getChildren[0]!
    let mut es := #[]
    for t in pf.getArguments[0]! do
      es := es.push (← reconstructTerm t)
    addThm (← reconstructTerm pf.getResult) (mkAppN xsF es)
  | .ALPHA_EQUIV =>
    let α : Q(Type) ← reconstructSort pf.getResult[0]!.getSort
    let t  : Q($α) ← reconstructTerm pf.getResult[0]!
    let t' : Q($α) ← reconstructTerm pf.getResult[1]!
    addThm q($t = $t') q(Eq.refl $t)
  | _ => return none
where
  reconstructForallCong (pf : cvc5.Proof) : ReconstructM Expr := do
    let mv ← getCurrGoal
    mv.withContext do
      let n := reconstructQuant.getVariableName pf.getArguments[1]![0]!
      let α : Q(Type) ← reconstructSort pf.getArguments[1]![0]!.getSort
      let mkLam n α t := Meta.withLocalDeclD n α (reconstructTerm t >>= liftM ∘ Meta.mkLambdaFVars #[·])
      let p : Q($α → Prop) ← mkLam n α pf.getResult[0]![1]!
      let q : Q($α → Prop) ← mkLam n α pf.getResult[1]![1]!
      let h : Q(∀ a, $p a = $q a) ← Meta.mkFreshExprMVar q(∀ a, $p a = $q a)
      let (fv, mv') ← h.mvarId!.intro n
      let a : Q($α) ← (return .fvar fv)
      setCurrGoal mv'
      let h' : Q($p $a = $q $a) ← mv'.withContext (withAssums #[a] (reconstructProof pf.getChildren[0]!))
      let mv' ← getCurrGoal
      mv'.withContext (mv'.assignIfDefeq h')
      setCurrGoal mv
      addThm q((∀ a, $p a) = (∀ a, $q a)) q(forall_congr $h)
  reconstructSkolemize (pf : cvc5.Proof) : ReconstructM Expr := do
    let res := pf.getChildren[0]!.getResult
    if res.getKind == .EXISTS then
      let es ← reconstructQuant.reconstructExistsSkolems res (res[0]![0]!.getNumChildren - 1)
      let f := fun h e => do
        let α : Q(Type) ← pure (e.getArg! 0)
        let hα : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
        let p : Q($α → Prop)  ← pure (e.getArg! 2)
        let h : Q(∃ x, $p x) ← pure h
        return q(@Classical.epsilon_spec_aux $α $hα $p $h)
      let h : Expr ← es.foldlM f (← reconstructProof pf.getChildren[0]!)
      addThm (← reconstructTerm pf.getResult) h
    else
      let es ← reconstructQuant.reconstructForallSkolems res (res[0]![0]!.getNumChildren - 1)
      let f := fun h e => do
        let α : Q(Type) ← pure (e.getArg! 0)
        let hα : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
        let .lam n _ (.app _ b) bi := e.getArg! 2 | throwError "[skolemize]: expected a predicate with a negated body: {e}"
        let p : Q($α → Prop)  ← pure (.lam n α b bi)
        let h : Q(¬∀ x, $p x) ← pure h
        return q(@Classical.epsilon_spec_aux' $α $hα $p $h)
      let h : Expr ← es.foldlM f (← reconstructProof pf.getChildren[0]!)
      addThm (← reconstructTerm pf.getResult) h

end Smt.Reconstruct.Quant
