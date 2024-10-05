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
  let e ← if xs.isEmpty then return e else liftMkBindingM <| MetavarContext.mkLambda xs e usedOnly (etaReduce := false) usedLetOnly binderInfoForMVars
  addExists e xs.size
where
  addExists : Expr → Nat → MetaM Expr
    | .lam n t b i, m + 1 => do
      let b ← addExists b m
      mkAppM ``Exists #[.lam n t b i]
    | e, _ => pure e

namespace Smt.Reconstruct.Quant

open Lean Qq

def getVariableName (t : cvc5.Term) : Name :=
  if t.hasSymbol then
    if t.getSymbol.toName == .anonymous then
      Name.mkSimple t.getSymbol
    else
      t.getSymbol.toName
  else Name.num `x t.getId

@[smt_term_reconstruct] def reconstructQuant : TermReconstructor := fun t => do match t.getKind with
  | .FORALL =>
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let b ← reconstructTerm t[1]!
      Meta.mkForallFVars xs b
  | .EXISTS =>
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let b ← reconstructTerm t[1]!
      Meta.mkExistsFVars xs b
  | .LAMBDA =>
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let b ← reconstructTerm t[1]!
      Meta.mkLambdaFVars xs b
  | .HO_APPLY =>
    return (← reconstructTerm t[0]!).app (← reconstructTerm t[1]!)
  | .SKOLEM => match t.getSkolemId with
    | .QUANTIFIERS_SKOLEMIZE =>
      let q := t.getSkolemIndices[0]!
      let n := t.getSkolemIndices[1]!.getIntegerValue.toNat
      let es ← reconstructForallSkolems q n
      return es[n]!
    | _ => return none
  | _ => return none
where
  reconstructForallSkolems (q : cvc5.Term) (n : Nat) : ReconstructM (Array Expr) := do
    let mut xs : Array (Name × (Array Expr → ReconstructM Expr)) := #[]
    let mut es := #[]
    for x in q[0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    let F := q[1]!
    for i in [0:n + 1] do
      let α : Q(Type) ← reconstructSort q[0]![i]!.getSort
      let h : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
      let e ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
        let F ← reconstructTerm F
        let ysF : Q(Prop) ← Meta.mkForallFVars xs[i + 1:] F
        let xysF ← Meta.mkLambdaFVars #[xs[i]!] q(¬$ysF)
        let xysF : Q($α → Prop) := xysF.replaceFVars xs[0:i] es
        return q(@Classical.epsilon $α $h $xysF)
      es := es.push e
    return es

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule with
  | .BETA_REDUCE =>
    let α : Q(Type) ← reconstructSort pf.getResult[0]!.getSort
    let t  : Q($α) ← reconstructTerm pf.getResult[0]!
    let t' : Q($α) ← reconstructTerm pf.getResult[1]!
    addThm q($t = $t') q(Eq.refl $t)
  | .EXISTS_ELIM =>
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    let ((q : Q(Prop)), (p : Q(Prop)), (h : Q((¬$q) = $p))) ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let b : Q(Prop) ← reconstructTerm pf.getResult[0]![1]!
      let h := q(Classical.not_not_eq $b)
      let f := fun x (p, q, h) => do
        let α : Q(Type) ← Meta.inferType x
        let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[x] p
        let lq : Q($α → Prop) ← Meta.mkLambdaFVars #[x] q
        let hx : Q(∀ x : $α, (¬$lp x) = $lq x) ← Meta.mkLambdaFVars #[x] h
        let ap ← Meta.mkForallFVars #[x] p
        let eq ← Meta.mkExistsFVars #[x] q
        return (ap, eq, q(Eq.trans (Classical.not_forall_eq $lp) (congrArg Exists (funext $hx))))
      xs.foldrM f (q(¬$b), b, h)
    addThm q($p = ¬$q) q(@Eq.symm Prop (¬$q) $p $h)
  | .QUANT_UNUSED_VARS =>
    let mut ys := #[]
    if pf.getResult[1]!.getKind == .FORALL then
      for y in pf.getResult[1]![0]! do
        ys := ys.push (getVariableName y, fun _ => reconstructSort y.getSort)
    let (_, p, q, h) ← Meta.withLocalDeclsD ys fun ys => withNewTermCache do
      let b : Q(Prop) ← reconstructTerm pf.getResult[0]![1]!
      let h : Q($b = $b) := q(Eq.refl $b)
      let f := fun i (j, p, q, (h : Q($p = $q))) => do
        let α : Q(Type) ← reconstructSort pf.getResult[0]![0]![i]!.getSort
        if let some j := j then
          if pf.getResult[0]![0]![i]! == pf.getResult[1]![0]![j]! then
            let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[ys[j]!] p
            let lq : Q($α → Prop) ← Meta.mkLambdaFVars #[ys[j]!] q
            let hx : Q(∀ x : $α, $lp x = $lq x) ← Meta.mkLambdaFVars #[ys[j]!] h
            let ap ← Meta.mkForallFVars #[ys[j]!] p
            let aq ← Meta.mkForallFVars #[ys[j]!] q
            return (if j == 0 then none else some (j - 1), ap, aq, q(forall_congr $hx))
        let hα : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
        let ap := .forallE (getVariableName pf.getResult[0]![0]![i]!) α p .default
        return (j, ap, q, q(@forall_const_eq $α $hα $p $q $h))
      let i := pf.getResult[0]![0]!.getNumChildren
      let j := if ys.isEmpty then none else some (ys.size - 1)
      (List.range i).foldrM f (j, b, b, h)
    addThm q($p = $q) h
  | .QUANT_MERGE_PRENEX =>
    let α : Q(Type) ← reconstructSort pf.getResult[0]!.getSort
    let t  : Q($α) ← reconstructTerm pf.getResult[0]!
    let t' : Q($α) ← reconstructTerm pf.getResult[1]!
    addThm q($t = $t') q(Eq.refl $t)
  | .QUANT_MINISCOPE =>
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    let (_, _, h) ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let mut ps : Array Q(Prop) := #[]
      for ct in pf.getResult[0]![1]! do
        let p : Q(Prop) ← reconstructTerm ct
        ps := ps.push q($p)
      let b : Q(Prop) ← reconstructTerm pf.getResult[0]![1]!
      let h : Q($b = $b) := q(Eq.refl $b)
      let lf := fun x (α : Q(Type)) p lps => do
        let lp : Q($α → Prop) ← (return ← Meta.mkLambdaFVars #[x] p)
        return q($lp :: $lps)
      let f := fun x (p, ps, h) => do
        let α : Q(Type) ← Meta.inferType x
        let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[x] p
        let lps : Q(List ($α → Prop)) ← ps.foldrM (lf x α) q([])
        let hx : Q(∀ x, $lp x = andN («$lps».map (· x))) ← Meta.mkLambdaFVars #[x] h
        let ap ← Meta.mkForallFVars #[x] p
        let aps ← liftM (ps.mapM (Meta.mkForallFVars #[x]))
        return (ap, aps, q(Eq.trans (forall_congr $hx) (@miniscopeN $α $lps)))
      xs.foldrM f (b, ps, h)
    addThm (← reconstructTerm pf.getResult) h
  | _ => return none

@[smt_proof_reconstruct] def reconstructQuantProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .THEORY_REWRITE => reconstructRewrite pf
  | .CONG =>
    let k := pf.getResult[0]!.getKind
    -- This rule needs more care for closures.
    if k == .FORALL then
      reconstructForallCong pf
    else if k == .EXISTS then
      reconstructExistsCong pf
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
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    let (p, q, h) ← Meta.withLocalDeclsD xs fun xs => withNewTermCache <| withNewProofCache <| withAssums xs do
      let p : Q(Prop) ← reconstructTerm pf.getResult[0]![1]!
      let q : Q(Prop) ← reconstructTerm pf.getResult[1]![1]!
      let h : Q($p = $q) ← reconstructProof pf.getChildren[0]!
      let f := fun x (p, q, h) => do
        let α : Q(Type) ← Meta.inferType x
        let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[x] p
        let lq : Q($α → Prop) ← Meta.mkLambdaFVars #[x] q
        let hx : Q(∀ x : $α, $lp x = $lq x) ← Meta.mkLambdaFVars #[x] h
        let ap ← Meta.mkForallFVars #[x] p
        let aq ← Meta.mkForallFVars #[x] q
        return (ap, aq, q(forall_congr $hx))
      xs.foldrM f (p, q, h)
    addThm q($p = $q) h
  reconstructExistsCong (pf : cvc5.Proof) : ReconstructM Expr := do
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    let (p, q, h) ← Meta.withLocalDeclsD xs fun xs => withNewTermCache <| withNewProofCache <| withAssums xs do
      let p : Q(Prop) ← reconstructTerm pf.getResult[0]![1]!
      let q : Q(Prop) ← reconstructTerm pf.getResult[1]![1]!
      let h : Q($p = $q) ← reconstructProof pf.getChildren[0]!
      let f := fun x (p, q, h) => do
        let α : Q(Type) ← Meta.inferType x
        let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[x] p
        let lq : Q($α → Prop) ← Meta.mkLambdaFVars #[x] q
        let hx : Q(∀ x : $α, $lp x = $lq x) ← Meta.mkLambdaFVars #[x] h
        let ep ← Meta.mkExistsFVars #[x] p
        let eq ← Meta.mkExistsFVars #[x] q
        return (ep, eq, q(exists_congr_eq $hx))
      xs.foldrM f (p, q, h)
    addThm q($p = $q) h
  reconstructSkolemize (pf : cvc5.Proof) : ReconstructM Expr := do
    let chRes := pf.getChildren[0]!.getResult
    let es ← reconstructQuant.reconstructForallSkolems chRes[0]! (chRes[0]![0]!.getNumChildren - 1)
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
