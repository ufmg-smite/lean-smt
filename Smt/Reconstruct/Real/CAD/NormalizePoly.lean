import Mathlib
import Lean
import CompPoly

section test

open CompPoly

def p1 : CPolynomial Int := CPolynomial.X

example (a : Int) : a < 0 → p1.eval a < 0 := by
  intro h
  simp [p1, CPolynomial.eval, CPolynomial.Raw.eval, CPolynomial.Raw.eval₂, CPolynomial.X, CPolynomial.Raw.X]
  exact h

def p2 : CPolynomial Int := CPolynomial.X + CPolynomial.C 1

lemma eval_add (a : Int) (p q : CPolynomial Int) : (p + q).eval a = p.eval a + q.eval a := by
  rw [CPolynomial.eval_toPoly, CPolynomial.eval_toPoly, CPolynomial.eval_toPoly, CPolynomial.toPoly_add]
  norm_num

lemma eval_id (a : Int) : CPolynomial.X.eval a = a := by
  rw [CPolynomial.eval_toPoly, CPolynomial.X_toPoly]
  norm_num

lemma eval_pow_r (a : Int) (r : Nat) : CPolynomial.eval a (CPolynomial.X ^ r) = a ^ r := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
  norm_num

lemma eval_smul (a c : Int) (p : CPolynomial Int) : (CPolynomial.C c * p).eval a = c * p.eval a := by
  rw [CPolynomial.eval_toPoly, CPolynomial.eval_toPoly, CPolynomial.toPoly_mul, CPolynomial.C_toPoly]
  norm_num

lemma eval_const (a c : Int) : (CPolynomial.C c).eval a = c := by
  rw [CPolynomial.eval_toPoly, CPolynomial.C_toPoly]
  norm_num

instance : DecidableEq (CPolynomial Rat) := Subtype.instDecidableEq

end test

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

@[tactic simple_push_neg] def evalSimplePushNeg : Tactic := fun stx => withMainContext do
  let h ← elabTerm stx[1] none
  let h' ← push_not h
  let t ← inferType h'
  let mv ← getMainGoal
  let (_, mv) ← MVarId.intro1P $ ← mv.assert .anonymous t h'
  replaceMainGoal [mv]

example (a b : Real) : ¬ (32 * a - 4 < 45 * b^2 + b) → 32 * a -4 ≥ 45 * b ^ 2 + b := by
  intro h
  simple_push_neg h
  assumption

example (a b : Real) : ¬ (32 * a - 4 ≤ 45 * b^2 + b) → 32 * a -4 > 45 * b ^ 2 + b := by
  intro h
  simple_push_neg h
  assumption

example (a b : Real) : ¬ (32 * a - 4 > 45 * b^2 + b) → 32 * a -4 ≤ 45 * b ^ 2 + b := by
  intro h
  simple_push_neg h
  assumption

example (a b : Real) : ¬ (32 * a - 4 ≥ 45 * b^2 + b) → 32 * a -4 < 45 * b ^ 2 + b := by
  intro h
  simple_push_neg h
  assumption

example (a b : Real) : ¬ (32 * a - 4 = 45 * b^2 + b) → 32 * a -4 ≠ 45 * b ^ 2 + b := by
  intro h
  exact h

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
  | .app (.app (.app (.app (.const `GE.ge ..) _) _) _) _ => mkAppM ``sub_nonneg_of_le #[h]
  | .app (.app (.app (.const ``Eq ..) _) _) _ => mkAppM ``sub_eq_zero_of_eq #[h]
  | _ => throwError "[all_to_lhs]: impossible"

@[tactic normalize_rel] def evalNormalizeRel : Tactic := fun stx => withMainContext do
  let h ← elabTerm stx[1] none
  let h' ← all_to_lhs h
  let t ← inferType h'
  let mv ← getMainGoal
  let (_, mv) ← MVarId.intro1P $ ← mv.assert .anonymous t h'
  replaceMainGoal [mv]

example (a b : Rat) : (a ^ 2 + 3 * a - 24 = b * 23 + a) → True := by
  intro h
  normalize_rel h
  exact True.intro

open Mathlib.Tactic.RingNF in
def ring_compute_norm (e : Expr) : MetaM (Expr × Expr) := do
  let rawResult ← Mathlib.Tactic.AtomM.recurse (← IO.mkRef {}) default (wellBehavedDischarge := true) evalExpr (cleanup default) e
  match rawResult.proof? with
  | none =>
    throwError "ring nf failed"
  | some p =>
    return ⟨rawResult.expr, p⟩

syntax (name := meta_norm) "meta_norm" term : tactic


/-- Given:
  - `h1 : P`  (a proof of some proposition)
  - `h2 : a = b`  (a proof of some equality)
  Produces `h1' : P[a ↦ b]`, i.e. `h1` rewritten left-to-right by `h2` everywhere. -/
def rewriteWithEq (h1 h2 : Expr) : MetaM Expr := do
  let prop ← inferType h1
  let eqType ← inferType h2
  let some (α, a, b) := eqType.eq?
    | throwError "rewriteWithEq: h2 is not a proof of an equality, got {eqType}"
  let motive ← kabstract prop a
  if motive == prop then
    return h1
  let newProp := motive.instantiate1 b
  let motiveExpr := mkLambda `x .default α motive
  let h1' ← mkAppOptM ``Eq.subst #[none, motiveExpr, a, b, h2, h1]
  check h1'
  let h1'Type ← inferType h1'
  unless ← isDefEq h1'Type newProp do
    throwError "rewriteWithEq: type mismatch, expected {newProp} but got {h1'Type}"
  return h1'

def ring_normalize (h : Expr) : MetaM Expr := do
  let t ← inferType h
  let ⟨_, eq_pf⟩ ← ring_compute_norm t
  rewriteWithEq h eq_pf


@[tactic meta_norm] def evalMetaNorm : Tactic := fun stx => withMainContext do
  let h ← elabTerm stx[1] none
  let h' ← ring_normalize h

  let t ← inferType h'
  let mv ← getMainGoal
  let (_, mv) ← MVarId.intro1P $ ← mv.assert .anonymous t h'
  replaceMainGoal [mv]

example (a : Real) : a ^ 2 - 3 * a + a * a - a + 2 = 0 → False := by
  intro h
  meta_norm h
  admit

/- example (α : Type) (a b : |a) -/

/- example (a : Rat) : (34 * a ^ 2 + 1) - (32 * a ^ 2 + a - 3) = 0 → False := by -/
/-   intro h -/
/-   rw [h] -/
/-   admit -/
