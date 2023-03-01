import Lean

import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.Options
import Smt.Reconstruction.Certifying.Util

open Lean Elab Tactic Meta Expr
open List


def getGroupOrPrefixGoal : Expr → Nat → Expr
| e, n => let props := collectPropsInOrChain e
          let left := createOrChain (take n props)
          let right := createOrChain (drop n props)
          app (app (mkConst `Or) left) right

-- groups the given prefix of the given hypothesis (assuming it is an
-- or-chain) and adds this as a new hypothesis with the given name
def groupOrPrefixCore (hyp type : Expr) (prefLen : Nat) (name : Name)
  : TacticM Unit := withMainContext do
    let l := getLength type
    if prefLen > 0 && prefLen < l then
      let mvarId ← getMainGoal
      MVarId.withContext mvarId do
        let newTerm := getGroupOrPrefixGoal type prefLen
        let p ← Meta.mkFreshExprMVar newTerm MetavarKind.syntheticOpaque name
        let (_, mvarIdNew) ← MVarId.intro1P $ ← MVarId.assert mvarId name newTerm p
        replaceMainGoal [p.mvarId!, mvarIdNew]
      for t in reverse (getCongAssoc (prefLen - 1) `orAssocDir) do
        evalTactic  (← `(tactic| apply $t))
      Tactic.closeMainGoal hyp
    else throwError
           "[groupOrPrefix]: prefix length must be > 0 and < size of or-chain"

syntax (name := liftOrNToImp) "liftOrNToImp" term "," term : tactic

@[tactic liftOrNToImp] def evalLiftOrNToImp : Tactic :=
  fun stx => do
    let startTime ← IO.monoMsNow
    withMainContext do
      let prefLen ← stxToNat ⟨stx[3]⟩
      let fname1 ← mkFreshId
      let fident1 := mkIdent fname1
      let hyp ← Tactic.elabTerm stx[1] none
      let type ← inferType hyp
      if prefLen > 1 then
        groupOrPrefixCore hyp type prefLen fname1
      else
        evalTactic (← `(tactic| have $fident1 := $(⟨stx[1]⟩)))
      let fname2 ← mkIdent <$> mkFreshId
      evalTactic (← `(tactic| intros $fname2))
      evalTactic (← `(tactic| apply orImplies₃ $fident1))
      let expandedType ← expandTypesInOrChain type
      let li :=
        listExpr (collectOrNNegArgs expandedType prefLen) (sort Level.zero)
      withMainContext do
        let ctx ← getLCtx
        let hyp2 := (ctx.findFromUserName? fname2.getId).get!.toExpr
        Tactic.closeMainGoal $ mkApp (mkApp (mkConst `deMorgan₂) li) hyp2
    let endTime ← IO.monoMsNow
    trace[smt.profile] m!"[liftOrNToImp] Time taken: {endTime - startTime}ms"

universe u
variable {U : Type u}
variable {f : U → U → U}
variable {p₁ p₂ p₃ : Prop}
variable {a b c d : U}

theorem euf :
  let let1 := a = b
  let let2 := c = d
  let let3 := p₁ ∧ True
  let let4 := p₂ ∧ p₃
  let let5 := (¬ p₁ ∨ p₄)
  let let6 := f a c = f b d
  let let7 := ¬ let6
  let let8 := (¬ p₃) ∨ let7
  let let9 := ¬ let4
  let let10 := ¬ let2
  let let11 := ¬ let1
  let let12 := let1 ∧ let2
  let1 → let2 → let3 → let5 → let8 → False := by
    intros let1 let2 let3 let4 let5 let6 let7 let8 let9 let10 let11 let12
    intros lean_a0 lean_a1 lean_a2 lean_a3 lean_a4
    have lean_s0 : let12 ∨ let11 ∨ let10 := cnfAndNeg [let1, let2]
    have lean_s1 : let11 ∨ let10 ∨ let6 :=
      scope (λ lean_a5 : let1 =>
        (scope (λ lean_a6 : let2 =>
          let lean_s1 : f = f := rfl
          have lean_s2 : b = a := Eq.symm lean_a5
          have lean_s3 : let1 := Eq.symm lean_s2
          let lean_s4 := congr lean_s1 lean_s3
          have lean_s5 : d = c := Eq.symm lean_a6
          have lean_s6 : let2 := Eq.symm lean_s5
          have lean_s7 : let6 := congr lean_s4 lean_s6
          show let6 from lean_s7
        )
      ))
    /- have lean_s2 : let12 → let6 := by -/
    /-   have fname1 := orAssocDir lean_s1 -/
    /-   intro fname2 -/
    /-   apply orImplies₃ fname1 -/
    /-   exact @deMorgan₂ [let1, let2] fname2 -/
    have lean_s2 : let12 → let6 := by liftOrNToImp lean_s1, 2
    have lean_s3 : (¬ let12) ∨ let6 := impliesElim lean_s2
    admit
