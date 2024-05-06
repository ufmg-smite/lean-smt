/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct
import Smt.Reconstruct.Quant.Lemmas

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
  | .SKOLEM => match t.getSkolemId with
    | .QUANTIFIERS_SKOLEMIZE =>
      let q := t.getSkolemIndices[0]!
      let x := t.getSkolemIndices[1]!
      let n := getVariableIndex q x
      let es ← if q.getKind == .EXISTS then reconstructExistsSkolems q n else reconstructForallSkolems q n
      return es[n]!
    | _ => return none
  | _ => return none
where
  getVariableIndex (q : cvc5.Term) (x : cvc5.Term) : Nat := Id.run do
    let xs := q[0]!
    let mut i := 0
    while xs[i]! != x do
      i := i + 1
    i
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

def reconstructRewrite (pf : cvc5.Proof) (cpfs : Array Expr) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule with
  | .BETA_REDUCE =>
    let α : Q(Type) ← reconstructSort pf.getResult[0]!.getSort
    let t  : Q($α) ← reconstructTerm pf.getResult[0]!
    let t' : Q($α) ← reconstructTerm pf.getResult[1]!
    addThm q($t = $t') q(Eq.refl $t)
  | .EXISTS_ELIM =>
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (reconstructQuant.getVariableName x, fun _ => reconstructSort x.getSort)
    let p : Q(Prop) ← reconstructTerm pf.getResult[0]!
    let q : Q(Prop) ← reconstructTerm pf.getResult[1]!
    let (_, _, (h : Q($q = $p))) ← Meta.withLocalDeclsD xs fun xs => do
      let b : Q(Prop) ← reconstructTerm pf.getResult[0]![1]!
      let h := q(Classical.not_not_eq $b)
      let f : Expr → (Expr × Expr × Expr) → ReconstructM (Expr × Expr × Expr) := fun x (p, q, h) => do
        let α : Q(Type) ← Meta.inferType x
        let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[x] p
        let lq : Q($α → Prop) ← Meta.mkLambdaFVars #[x] q
        let hx : Q(∀ x : $α, (¬$lp x) = $lq x) ← Meta.mkLambdaFVars #[x] h
        let ap ← Meta.mkForallFVars #[x] p
        let eq ← Meta.mkExistsFVars #[x] q
        return (ap, eq, q(Eq.trans (Classical.not_forall_eq $lp) (congrArg Exists (funext $hx))))
      xs.foldrM f (q(¬$b), q($b), h)
    addThm q($p = $q) q(@Eq.symm Prop $q $p $h)
  | _ => return none

@[smt_proof_reconstruct] def reconstructQuantProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .THEORY_REWRITE => reconstructRewrite pf (← pf.getChildren.mapM reconstructProof)
  | .CONG =>
    let k := pf.getResult[0]!.getKind
    -- This rule needs more care for closures.
    if k == .FORALL then
      reconstructForallCong pf
    else
      return none
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
    let n := reconstructQuant.getVariableName pf.getArguments[1]![0]!
    let α : Q(Type) ← reconstructSort pf.getArguments[1]![0]!.getSort
    let mkLam n α t := withNewTermCache $ Meta.withLocalDeclD n α (reconstructTerm t >>= liftM ∘ Meta.mkLambdaFVars #[·])
    let p : Q($α → Prop) ← mkLam n α pf.getResult[0]![1]!
    let q : Q($α → Prop) ← mkLam n α pf.getResult[1]![1]!
    let h : Q(∀ a, $p a = $q a) ← Meta.mkFreshExprMVar q(∀ a, $p a = $q a)
    let (fv, mv) ← h.mvarId!.intro n
    withNewProofCache $ withNewTermCache $ mv.withContext do
      let a : Q($α) ← (return .fvar fv)
      let h' : Q($p $a = $q $a) ← withAssums #[a] (reconstructProof pf.getChildren[0]!)
      mv.assign (← instantiateMVars h')
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
