import Mathlib
import Lean
import CompPoly

import Smt.Reconstruct.Real.CAD.Utils

theorem not_lt_mp {α : Type*} [LinearOrder α] {a b : α} : ¬ (a < b) → a ≥ b := not_lt.mp
theorem not_le_mp {α : Type*} [LinearOrder α] {a b : α} : ¬ (a ≤ b) → a > b := not_le.mp

open Qq Lean Elab Tactic Meta

syntax (name := simple_push_neg) "simple_push_neg" term : tactic

def push_not (h : Expr) : MetaM Expr := do
  let t ← inferType h
  match t with
  | .app (.const `Not ..) e =>
    match e with
    | .app (.app (.app (.app (.const `LT.lt ..) _) _) _) _ => mkAppM `not_lt_mp #[h]
    | .app (.app (.app (.app (.const `LE.le ..) _) _) _) _ => mkAppM `not_le_mp #[h]
    | .app (.app (.app (.app (.const `GT.gt ..) _) _) _) _ => mkAppM `not_lt_mp #[h]
    | .app (.app (.app (.app (.const `GE.ge ..) _) _) _) _ => mkAppM `not_le_mp #[h]
    | .app (.app (.app (.const ``Eq ..) _) _) _ => return h -- hmm
    | _ =>
      throwError "[simple_push_neg]: impossible"
  | _ => return h

syntax (name := normalize_rel) "normalize_rel" term : tactic

lemma sub_neg_mpr {α : Type*} [CommRing α] [LinearOrder α] [AddRightStrictMono α] {a b : α} : a < b → a - b < 0 := sub_neg.mpr
lemma tsub_nonpos_mpr {α : Type*} [CommRing α] [LinearOrder α] [AddRightMono α] {a b : α} : a ≤ b → a - b ≤ 0 := tsub_nonpos.mpr
lemma sub_pos_mpr {α : Type*} [CommRing α] [LinearOrder α] [AddRightStrictMono α] {a b : α} : a > b → a - b > 0 := sub_pos.mpr

def all_to_lhs (h : Expr) : MetaM Expr := do
  let t ← inferType h
  match t with
  | .app (.app (.app (.app (.const `LT.lt ..) _) _) _) _ => mkAppM ``sub_neg_mpr #[h]
  | .app (.app (.app (.app (.const `LE.le ..) _) _) _) _ => mkAppM ``tsub_nonpos_mpr #[h]
  | .app (.app (.app (.app (.const `GT.gt ..) _) _) _) _ => mkAppM ``sub_pos_mpr #[h]
  | .app (.app (.app (.app (.const `GE.ge ..) _) _) _) _ => mkAppM ``sub_nonpos_of_le #[h]
  | .app (.app (.app (.const ``Eq ..) _) _) _ => mkAppM ``sub_eq_zero_of_eq #[h]
  | _ => throwError "[all_to_lhs]: impossible"

@[tactic normalize_rel] def evalNormalizeRel : Tactic := fun stx => withMainContext do
  let h ← elabTerm stx[1] none
  let h' ← all_to_lhs h
  let t ← inferType h'
  let mv ← getMainGoal
  let (_, mv) ← MVarId.intro1P $ ← mv.assert .anonymous t h'
  replaceMainGoal [mv]

open Mathlib.Tactic.RingNF in
def ring_compute_norm (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let rawResult ← Mathlib.Tactic.AtomM.recurse (← IO.mkRef {}) default (wellBehavedDischarge := true) evalExpr (cleanup default) e
  match rawResult.proof? with
  | none =>
    return none
  | some p =>
    return some ⟨rawResult.expr, p⟩

syntax (name := meta_norm) "meta_norm" term : tactic

def ring_normalize (h : Expr) : MetaM Expr := do
  let t ← inferType h
  let res ← ring_compute_norm t
  match res with
  | some ⟨_, eq_pf⟩ => rewriteWithEq h eq_pf
  | _ => return h

@[tactic meta_norm] def evalMetaNorm : Tactic := fun stx => withMainContext do
  let h ← elabTerm stx[1] none
  let h' ← ring_normalize h

  let t ← inferType h'
  let mv ← getMainGoal
  let (_, mv) ← MVarId.intro1P $ ← mv.assert .anonymous t h'
  replaceMainGoal [mv]

/-- Swaps the sides of an order relation or equation: `0 > p` ↦ `p < 0`, `0 ≥ p` ↦ `p ≤ 0`,
`0 < p` ↦ `p > 0`, `0 ≤ p` ↦ `p ≥ 0` (all definitional), and `0 = p` ↦ `p = 0`. -/
def flipRel (pf : Expr) : MetaM Expr := do
  let t ← instantiateMVars (← inferType pf)
  match t with
  | .app (.app (.app (.app (.const ``GT.gt ls) α) i) a) b =>
    mkExpectedTypeHint pf (mkApp4 (.const ``LT.lt ls) α i b a)
  | .app (.app (.app (.app (.const ``GE.ge ls) α) i) a) b =>
    mkExpectedTypeHint pf (mkApp4 (.const ``LE.le ls) α i b a)
  | .app (.app (.app (.app (.const ``LT.lt ls) α) i) a) b =>
    mkExpectedTypeHint pf (mkApp4 (.const ``GT.gt ls) α i b a)
  | .app (.app (.app (.app (.const ``LE.le ls) α) i) a) b =>
    mkExpectedTypeHint pf (mkApp4 (.const ``GE.ge ls) α i b a)
  | .app (.app (.app (.const ``Eq _) _) _) _ => mkEqSymm pf
  | _ => throwError "[flipRel]: unsupported relation {t}"

/-- Turns a constraint over a variable into the same constraint over a polynomial evaluation.

Given `pf : p(x) ~ 0` or `pf : ¬ (p(x) ~ 0)`, with `~` one of `< ≤ > ≥ =` and `p(x)` the real
term obtained by reconstructing the cvc5 polynomial term of `P` at `x`, returns a proof of
`(toPolyReal P).eval x ~' 0`, always with the evaluation on the left and `0` on the right.
Negated order relations are pushed inwards (`¬ (p ≥ 0)` ↦ `eval < 0`, etc.), so `~'` is one of
`< ≤ > ≥ =`, or the result is `¬ (eval = 0)` for a disequality. -/
def liftConstraint (P : Q(CompPoly.CPolynomial Rat)) (x : Q(Real)) (pf : Expr) : MetaM Expr := do
  -- `¬ (p ≥ 0)` ↦ `0 > p`, etc.; `¬ (p = 0)` is left as is
  let pf ← push_not pf
  let t ← instantiateMVars (← inferType pf)
  let some (a, b) := relSides? t
    | throwError "[liftConstraint]: expected a relation, got {t}"
  -- make sure the polynomial is on the left and the literal `0` on the right
  let (pf, e) ←
    if ← isDefEq b q((0 : Real)) then pure (pf, a)
    else if ← isDefEq a q((0 : Real)) then pure (← flipRel pf, b)
    else throwError "[liftConstraint]: expected a comparison with 0, got {t}"
  -- `p(x)` ↦ `(toPolyReal P).eval x`
  let evalEq ← proveEvalEq P x e
  rewriteWithEq pf (← mkEqSymm evalEq)

namespace tests_lift_constraint

syntax (name := lift_constraint_tac) "lift_constraint" term "," term "," term : tactic

@[tactic lift_constraint_tac] def evalLiftConstraint : Tactic := fun stx => withMainContext do
  let P ← elabTerm stx[1] none
  let x ← elabTerm stx[3] none
  let h ← elabTerm stx[5] none
  closeMainGoal .anonymous (← liftConstraint P x h)

example (a : Real) (h : (-15) + 2 * a + 10 * a * a > 0) :
    (toPolyReal (CompPoly.CPolynomial.C (-15) + CompPoly.CPolynomial.C 2 * CompPoly.CPolynomial.X + CompPoly.CPolynomial.C 10 * CompPoly.CPolynomial.X ^ 2)).eval a > 0 := by
  lift_constraint (CompPoly.CPolynomial.C (-15) + CompPoly.CPolynomial.C 2 * CompPoly.CPolynomial.X + CompPoly.CPolynomial.C 10 * CompPoly.CPolynomial.X ^ 2 : CompPoly.CPolynomial Rat), a, h

-- `¬ (p ≥ 0)` becomes `eval < 0`, with the sides flipped back after `push_not`
example (a : Real) (h : ¬ ((-15) + 2 * a + 10 * a * a ≥ 0)) :
    (toPolyReal (CompPoly.CPolynomial.C (-15) + CompPoly.CPolynomial.C 2 * CompPoly.CPolynomial.X + CompPoly.CPolynomial.C 10 * CompPoly.CPolynomial.X ^ 2)).eval a < 0 := by
  lift_constraint (CompPoly.CPolynomial.C (-15) + CompPoly.CPolynomial.C 2 * CompPoly.CPolynomial.X + CompPoly.CPolynomial.C 10 * CompPoly.CPolynomial.X ^ 2 : CompPoly.CPolynomial Rat), a, h

-- `¬ (p > 0)` becomes `eval ≤ 0`
example (a : Real) (h : ¬ ((-2) + 1 * a > 0)) :
    (toPolyReal (CompPoly.CPolynomial.C (-2) + CompPoly.CPolynomial.C 1 * CompPoly.CPolynomial.X)).eval a ≤ 0 := by
  lift_constraint (CompPoly.CPolynomial.C (-2) + CompPoly.CPolynomial.C 1 * CompPoly.CPolynomial.X : CompPoly.CPolynomial Rat), a, h

-- disequality is kept as a negated equation
example (a : Real) (h : ¬ ((-2) + 1 * a = 0)) :
    ¬ ((toPolyReal (CompPoly.CPolynomial.C (-2) + CompPoly.CPolynomial.C 1 * CompPoly.CPolynomial.X)).eval a = 0) := by
  lift_constraint (CompPoly.CPolynomial.C (-2) + CompPoly.CPolynomial.C 1 * CompPoly.CPolynomial.X : CompPoly.CPolynomial Rat), a, h

end tests_lift_constraint
