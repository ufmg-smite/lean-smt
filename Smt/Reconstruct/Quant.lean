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
    if t.getSymbol!.toName == .anonymous then
      Name.mkSimple t.getSymbol!
    else
      t.getSymbol!.toName
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
  | .SKOLEM => match t.getSkolemId! with
    | .QUANTIFIERS_SKOLEMIZE =>
      let q := t.getSkolemIndices![0]!
      let n := t.getSkolemIndices![1]!.getIntegerValue!.toNat
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
      let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort q[0]![i]!.getSort
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
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]!.getSort
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
        let u ← Meta.getLevel (← Meta.inferType x)
        let α : Q(Sort u) ← Meta.inferType x
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
        let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]![0]![i]!.getSort
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
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]!.getSort
    let t  : Q($α) ← reconstructTerm pf.getResult[0]!
    let t' : Q($α) ← reconstructTerm pf.getResult[1]!
    addThm q($t = $t') q(Eq.refl $t)
  | .QUANT_MINISCOPE_AND =>
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
      let lf := fun x (u, (α : Q(Sort u))) p lps => do
        let lp : Q($α → Prop) ← (return ← Meta.mkLambdaFVars #[x] p)
        return .app q(PList.cons $lp) lps
      let f := fun x (p, ps, h) => do
        let u ← Meta.getLevel (← Meta.inferType x)
        let α : Q(Sort u) ← Meta.inferType x
        let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[x] p
        let (lps : Q(PList ($α → Prop))) ← ps.foldrM (lf x (u, α)) q(@PList.nil ($α → Prop))
        let hx : Q(∀ x, $lp x = pAndN («$lps».map (· x))) ← Meta.mkLambdaFVars #[x] h
        let ap ← Meta.mkForallFVars #[x] p
        let aps ← liftM (ps.mapM (Meta.mkForallFVars #[x]))
        return (ap, aps, q(Eq.trans (forall_congr $hx) (@miniscope_andN $α $lps)))
      xs.foldrM f (b, ps, h)
    addThm (← reconstructTerm pf.getResult) h
  | .QUANT_MINISCOPE_OR =>
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    let (_, _, _, _, h) ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let mut xss := #[]
      let mut ci := 0
      for xsF in pf.getResult[1]! do
        if xsF.getKind == .FORALL then
          xss := xss.push xs[ci:ci + xsF[0]!.getNumChildren]
          ci := ci + xsF[0]!.getNumChildren
        else
          xss := xss.push xs[ci:ci]
      let ps : List Q(Prop) := (← pf.getResult[0]![1]!.getChildren.mapM reconstructTerm).toList
      let b : Q(Prop) ← reconstructTerm pf.getResult[0]![1]!
      let h : Q($b = $b) := q(Eq.refl $b)
      let fin := fun x (p, ps, q, rs, h) => do
        let u ← Meta.getLevel (← Meta.inferType x)
        let α : Q(Sort u) ← Meta.inferType x
        let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[x] p
        let lq : Q($α → Prop) ← Meta.mkLambdaFVars #[x] q
        let qps : Q(List Prop) ← pure (ps.foldr (fun (p : Q(Prop)) qps => q($p :: $qps)) q([]))
        let qrs : Q(List Prop) ← pure (rs.foldr (fun (r : Q(Prop)) qrs => q($r :: $qrs)) q([]))
        let hx : Q(∀ x, $lp x = orN ($qps ++ $lq x :: $qrs)) ← Meta.mkLambdaFVars #[x] h
        let ap ← Meta.mkForallFVars #[x] p
        let aq ← Meta.mkForallFVars #[x] q
        return (ap, ps, aq, rs, q(Eq.trans (forall_congr $hx) (@miniscope_orN $α $qps $lq $qrs)))
      let fout := fun xs (p, ps, q, rs, h) => do
        let (p, ps, q, rs, h) ← xs.foldrM fin (p, ps, q, rs, h)
        return (p, ps.dropLast, ps.getLastD q(False), q :: rs, h)
      xss.foldrM fout (b, ps.dropLast, ps.getLast!, [], h)
    addThm (← reconstructTerm pf.getResult) h
  | .QUANT_MINISCOPE_ITE =>
    let mut xs := #[]
    for x in pf.getResult[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => reconstructSort x.getSort)
    let (_, _, _, h) ← Meta.withLocalDeclsD xs fun xs => withNewTermCache do
      let c : Q(Prop) ← reconstructTerm pf.getResult[0]![1]![0]!
      let p : Q(Prop) ← reconstructTerm pf.getResult[0]![1]![1]!
      let q : Q(Prop) ← reconstructTerm pf.getResult[0]![1]![2]!
      let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
      let h : Q((ite $c $p $q) = (ite $c $p $q)) := q(Eq.refl (ite $c $p $q))
      let f := fun x (p, q, r, h) => do
        let u ← Meta.getLevel (← Meta.inferType x)
        let α : Q(Sort u) ← Meta.inferType x
        let lp : Q($α → Prop) ← Meta.mkLambdaFVars #[x] p
        let lq : Q($α → Prop) ← Meta.mkLambdaFVars #[x] q
        let lr : Q($α → Prop) ← Meta.mkLambdaFVars #[x] r
        let hx : Q(∀ x, $lr x = ite $c ($lp x) ($lq x)) ← Meta.mkLambdaFVars #[x] h
        let ap ← Meta.mkForallFVars #[x] p
        let aq ← Meta.mkForallFVars #[x] q
        let ar ← Meta.mkForallFVars #[x] r
        return (ap, aq, ar, q(Eq.trans (forall_congr $hx) (@miniscope_ite $α $c $hc $lp $lq)))
      xs.foldrM f (p, q, q(ite $c $p $q), h)
    addThm (← reconstructTerm pf.getResult) h
  | .QUANT_VAR_ELIM_EQ =>
    let lb := pf.getResult[0]![1]!
    if lb.getKind == .OR then
      let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort lb[0]![0]![0]!.getSort
      let n : Name := getVariableName lb[0]![0]![0]!
      let t : Q($α) ← reconstructTerm lb[0]![0]![1]!
      let p : Q($α → Prop) ← Meta.withLocalDeclD n α fun x => withNewTermCache do
        let mut b : Q(Prop) ← reconstructTerm lb[lb.getNumChildren - 1]!
        for i in [1:lb.getNumChildren - 1] do
          let p : Q(Prop) ← reconstructTerm lb[lb.getNumChildren - i - 1]!
          b := q($p ∨ $b)
        Meta.mkLambdaFVars #[x] b
      addThm (← reconstructTerm pf.getResult) q(@Quant.var_elim_eq_or $α $t $p)
    else
      let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort lb[0]![0]!.getSort
      let t : Q($α) ← reconstructTerm lb[0]![1]!
      addThm (← reconstructTerm pf.getResult) q(@Quant.var_elim_eq $α $t)
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
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort pf.getResult[0]!.getSort
    let t  : Q($α) ← reconstructTerm pf.getResult[0]!
    let t' : Q($α) ← reconstructTerm pf.getResult[1]!
    addThm q($t = $t') q(Eq.refl $t)
  | .QUANT_VAR_REORDERING =>
    let xs := pf.getResult[0]![0]!.getChildren
    let ys := pf.getResult[1]![0]!.getChildren
    let g xs := Id.run do
      let mut is : Std.HashMap cvc5.Term Expr := {}
      for h : i in [:xs.size] do
        is := is.insert xs[i] (.bvar (xs.size - i - 1))
      return is
    let (is, js) := (g xs, g ys)
    let (is, js) := (xs.map js.get!, ys.map is.get!)
    let f x h := do
      let n := getVariableName x
      let α ← reconstructSort x.getSort
      return .lam n α h .default
    let p : Q(Prop) ← reconstructTerm pf.getResult[0]!
    let q : Q(Prop) ← reconstructTerm pf.getResult[1]!
    let hpq ← ys.foldrM f (mkAppN (.bvar js.size) is)
    let hpq : Q($p → $q) ← pure (.lam `hp p hpq .default)
    let hqp ← xs.foldrM f (mkAppN (.bvar is.size) js)
    let hqp : Q($q → $p) ← pure (.lam `hq q hqp .default)
    addThm q($p = $q) q(propext ⟨$hpq, $hqp⟩)
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
        let u ← Meta.getLevel (← Meta.inferType x)
        let α : Q(Sort u) ← Meta.inferType x
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
        let u ← Meta.getLevel (← Meta.inferType x)
        let α : Q(Sort u) ← Meta.inferType x
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
      let u ← Meta.getLevel (e.getArg! 0)
      let α : Q(Sort u) ← pure (e.getArg! 0)
      let hα : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
      let .lam n _ (.app _ b) bi := e.getArg! 2 | throwError "[skolemize]: expected a predicate with a negated body: {e}"
      let p : Q($α → Prop)  ← pure (.lam n α b bi)
      let h : Q(¬∀ x, $p x) ← pure h
      return q(@Classical.epsilon_spec_aux' $α $hα $p $h)
    let h : Expr ← es.foldlM f (← reconstructProof pf.getChildren[0]!)
    addThm (← reconstructTerm pf.getResult) h

end Smt.Reconstruct.Quant
