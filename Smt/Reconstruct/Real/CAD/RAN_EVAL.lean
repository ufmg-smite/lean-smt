import Lean
import Qq
import Smt.Reconstruct
import Smt.Reconstruct.Real.CAD.LiftIneq
import Smt.Reconstruct.Real.CAD.Utils
import Smt.Reconstruct.Real.CAD.RootVal

import CompPoly

open Lean Meta Qq CompPoly

/-- Given `isRootPf : IsRoot P r` and `ineqPf : p(var) ~ 0` (or `¬ p(var) ~ 0`), where `p(var)`
is the reconstruction of the cvc5 polynomial term of `P` at `var`, proves `¬ (var = r)`.

Strategy (as in the example above): lift the literal to `(toPolyReal P).eval var ~ 0`, assume
`var = r` and substitute it, rewrite the evaluation to `0` using the root fact, and refute the
resulting relation between `0` and `0` with `norm_num`. -/
def ranEvalCore (var : Q(Real)) (root : RootVal) (isRootPf : Expr) (ineqPf : Expr) : Smt.ReconstructM Expr := do
  let r : Q(Real) ← root.toReal
  let isRootT ← instantiateMVars (← inferType isRootPf)
  let P : Q(CPolynomial Rat) := isRootT.getArg! 0
  -- `IsRoot P r` unfolds to `(toPolyReal P).eval r = 0`
  let isRootPf ← mkExpectedTypeHint isRootPf q((toPolyReal $P).eval $r = 0)
  -- `p(var) ~ 0` ↦ `(toPolyReal P).eval var ~ 0`
  let ineqPf ← liftConstraint P var ineqPf

  let goal : Q(Prop) := q(¬ ($var = $r))
  let goalMVar ← mkFreshExprMVar goal
  let (h, mvFalse) ← goalMVar.mvarId!.intro1P
  mvFalse.withContext do
    -- `eval var ~ 0` ↦ `eval r ~ 0` ↦ `0 ~ 0`
    let ineqPf ← rewriteWithEq ineqPf (.fvar h)
    let ineqPf ← rewriteWithEq ineqPf isRootPf
    let t ← inferType ineqPf
    let mvNeg ← mkFreshExprMVar (mkNot t)
    normNum mvNeg.mvarId!
    mvFalse.assign (← mkAppOptM ``absurd #[t, q(False), ineqPf, mvNeg])
  instantiateMVars goalMVar

namespace tests_ran_eval

open Elab Tactic

--                                  var    root   IsRoot pf  literal pf
syntax (name := ran_eval_tac) "ran_eval" term "," term "," term "," term : tactic

@[tactic ran_eval_tac] def evalRanEval : Tactic := fun stx => withMainContext do
  let var ← elabTerm stx[1] none
  let root ← elabTerm stx[3] none
  let isRootPf ← elabTerm stx[5] none
  let ineqPf ← elabTerm stx[7] none
  let rv ← RootVal.ofExpr root
  let pf ← ((ranEvalCore var rv isRootPf ineqPf).run {}).run' {}
  closeMainGoal .anonymous pf

-- p = 10 x² + 2 x - 15, in the shape cvc5 emits: sum of `c * x * ... * x` monomials
example (a : Real)
    (h1 : IsRoot (CPolynomial.C (-15) + CPolynomial.C 2 * CPolynomial.X + CPolynomial.C 10 * CPolynomial.X ^ 2) (ratToReal 1))
    (h2 : (-15) + 2 * a + 10 * a * a > 0) : ¬ (a = ratToReal 1) := by
  ran_eval a, (1 : Rat), h1, h2

-- negated literal `¬ (p ≥ 0)`, which `push_not` turns into `0 > p`
example (a : Real)
    (h1 : IsRoot (CPolynomial.C (-15) + CPolynomial.C 2 * CPolynomial.X + CPolynomial.C 10 * CPolynomial.X ^ 2) (ratToReal (3/2)))
    (h2 : ¬ ((-15) + 2 * a + 10 * a * a ≥ 0)) : ¬ (a = ratToReal (3/2)) := by
  ran_eval a, (3/2 : Rat), h1, h2

-- disequality literal
example (a : Real)
    (h1 : IsRoot (CPolynomial.C (-2) + CPolynomial.C 1 * CPolynomial.X) (ratToReal 2))
    (h2 : ¬ ((-2) + 1 * a = 0)) : ¬ (a = ratToReal 2) := by
  ran_eval a, (2 : Rat), h1, h2

end tests_ran_eval
