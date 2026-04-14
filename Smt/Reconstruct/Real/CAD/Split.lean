import Mathlib
import Lean.Elab.Tactic.Basic
import Qq

import CompPoly
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.AlgNum
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Order
import Smt.Reconstruct.Real.CAD.Utils

open Qq Lean Elab Tactic ToExpr Meta
open AlgebraicNumber

-- takes an expression with exactly one real free variable and bounds it with a lambda
def bound_var (e : Expr) : Expr :=
  let e' := go e 0
  Expr.lam .anonymous (mkConst `Real) e' BinderInfo.default
where
  go e idx := match e with
  | .app f x => .app (go f idx) (go x idx)
  | .fvar _ => .bvar idx
  | .lam n t b bi => .lam n t (go b (idx + 1)) bi
  | .forallE n t b bi => .forallE n t (go b (idx + 1)) bi
  | .letE n t v b d => .letE n t (go v idx) (go b (idx + 1)) d
  | .mdata d e => .mdata d (go e idx)
  | .proj t i e => .proj t i (go e idx)
  | e => e

@[simp]
def decomp' (l : List ℝ) (sl : l.SortedLT) (first : Bool) : List (Set ℝ) :=
  match l with
  | [] => []
  | [x] =>
    if first then (fun y => y < x) :: (fun y => y = x) :: (fun y => y > x) :: []
    else (fun y => y = x) :: (fun y => y > x) :: []
  | x :: y :: t =>
    if first then
      (fun z => z < x) :: (fun z => z = x) :: (fun z => z > x ∧ z < y) :: decomp' (y :: t) (by grind) false
    else
      (fun z => z = x) :: (fun z => z > x ∧ z < y) :: decomp' (y :: t) (by grind) false

@[simp]
def decomp (l : List ℝ) (sl : l.SortedLT) : List (Set ℝ) := decomp' l sl true

@[simp]
def decomp'_merge (l : List ℝ) (sl : l.SortedLT) : Set ℝ := (decomp' l sl false).foldr (fun s acc => s ∪ acc) ∅

@[simp]
def decomp_merge (l : List ℝ) (sl : l.SortedLT) : Set ℝ := (decomp l sl).foldr (fun s acc => s ∪ acc) ∅

lemma decomp'_covers (hd : ℝ) (tl : List ℝ) (sl : (hd :: tl).SortedLT) :
    decomp'_merge (hd :: tl) sl = fun x => x ≥ hd := by
  cases tl
  next =>
    simp only [decomp'_merge, decomp', Bool.false_eq_true, ↓reduceIte, gt_iff_lt, List.foldr_cons,
      List.foldr_nil, Set.union_empty, ge_iff_le]
    ext z
    constructor
    · intro h
      simp at h
      cases h
      next h =>
        have : z = hd := Real.ext_cauchy (congrArg Real.cauchy h)
        rw [this]
        have : hd ≤ hd := Std.IsPreorder.le_refl hd
        exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 => a_1) this
      next h =>
        have : hd < z := gt_iff_lt.mp h
        bound
    · intro h
      simp only [Set.mem_union]
      have : hd < z ∨ hd = z := Decidable.lt_or_eq_of_le h
      cases this
      next =>
        right
        tauto
      next =>
        left
        tauto
  next hd' tl' =>
    simp only [decomp'_merge, decomp', Bool.false_eq_true, ↓reduceIte, gt_iff_lt, List.foldr_cons,
      ge_iff_le]
    ext z
    constructor
    · intro H
      simp only [Set.mem_union] at H
      cases H
      next H1 =>
        have : z = hd := Real.ext_cauchy (congrArg Real.cauchy H1)
        rw [this]
        have : hd ≤ hd := Std.IsPreorder.le_refl hd
        exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 => a_1) this
      next H1 =>
        cases H1
        next H2 =>
          have : hd < z := gt_iff_lt.mp H2.1
          bound
        next H2 =>
          have := decomp'_covers hd' tl' (by grind)
          have := (Eq.to_iff (congrFun this z)).mp H2
          have foo : hd < hd' := by grind
          suffices hd ≤ z by finiteness
          linarith
    · intro H
      simp only [Set.mem_union]
      have : hd ≤ z := by finiteness
      have : hd < z ∨ hd = z := Decidable.lt_or_eq_of_le H
      cases this
      next H1 =>
        right
        cases lt_trichotomy z hd'
        next H2 =>
          left
          trivial
        next H2 =>
          right
          have := decomp'_covers hd' tl' (by grind)
          have := (Eq.to_iff (congrFun this z)).mpr (by grind)
          apply this
      next H1 =>
        left
        exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 => a_1) (Eq.symm H1)

lemma decomp_covers (l : List ℝ) (sl : l.SortedLT) (hl : l ≠ []) :
    decomp_merge l sl = (Set.univ : Set ℝ) :=
  match l with
  | [] => Set.eq_univ_of_univ_subset fun ⦃a⦄ a_1 => hl rfl
  | [x] => by
    simp
    ext z
    constructor
    · exact fun a => Set.mem_univ z
    · intro _
      simp
      cases lt_trichotomy z x
      next h =>
        left
        finiteness
      next h =>
        right
        finiteness
  | x :: y :: t => by
    simp
    ext z
    constructor
    · exact fun a => Set.mem_univ z
    · intro _
      simp
      cases lt_trichotomy z x
      next h => tauto
      next h =>
        right
        cases h
        next h1 => exact Or.symm (Or.inr h1)
        next h1 =>
          right
          cases lt_trichotomy z y
          next h2 => tauto
          next h2 =>
            right
            have := decomp'_covers y t (by grind)
            have := (Eq.to_iff (congrFun this z)).mpr (by grind)
            apply this

lemma not_in_fold_sets (x : ℝ) (l : List (Set ℝ)) :
    (∀ p ∈ l, x ∉ p) → x ∉ l.foldr (fun s acc => s ∪ acc) ∅ := by
  intro h
  cases l
  next => simp
  next hd tl =>
    intro abs
    simp at abs
    cases abs
    next abs' =>
      have := h hd (by grind)
      exact this abs'
    next abs' =>
      have : ∀ p ∈ tl, x ∉ p := by grind
      have := not_in_fold_sets x tl this
      exact (iff_false_intro this).mp abs'

lemma in_component (x : ℝ) (l : List ℝ) (sl : l.SortedLT) (hl : l ≠ []) :
    ∃ p ∈ decomp l sl, x ∈ p := by
  by_contra! h
  have foo := decomp_covers l sl hl
  unfold decomp_merge at foo
  have := not_in_fold_sets x (decomp l sl) h
  simp_all only [ne_eq, decomp, Set.mem_univ, not_true_eq_false]

theorem in_component_prop {P : ℝ → Prop} (l : List ℝ) (sl : l.SortedLT) (hl : l ≠ []) (x : ℝ) :
    P x → (∃ p : Set Real, p ∈ decomp l sl ∧ (x ∈ p ∧ P x)) := by
  intro hx
  obtain ⟨p, hp⟩ := in_component x l sl hl
  tauto

-- given the list of roots and a proof that `P x` produces a proof
-- that `∃ p ∈ decomp roots, x ∈ p ∧ P x`, where `decomp roots` is the decomposition
-- of the real line into intervals separated at the roots.
def getDecompPf (x : Q(Real)) (roots: Q(List Real)) (roots_sorted_pf : Expr) : MetaM Expr := do
  let roots_not_empty : Q(Prop) := q($roots ≠ [])
  let roots_not_empty_pf ← Meta.mkFreshExprMVar roots_not_empty
  let ok ← runGrind roots_not_empty_pf.mvarId!
  if !ok then throwError "grind failed 8"
  Meta.mkAppOptM ``in_component #[x, roots, roots_sorted_pf, roots_not_empty_pf]

def collectDisjuncts (e: Expr) : List Expr :=
  match e with
  | .app (.app (.const `Or ..) lhs) rhs =>
    lhs :: collectDisjuncts rhs
  | _ => [e]

def go (imps: List Expr) (or_pf: Expr) : MetaM Expr := do
  match imps with
  | [] => throwError ""
  | [_] => return or_pf
  | [e1, e2] =>
    Meta.mkAppM `Or.elim #[or_pf, e1, e2]
  | e :: t => do
    let or_ty ← Meta.inferType or_pf
    match or_ty with
    | .app (.app (.const `Or ..) _) B =>
      Meta.withLocalDeclD .anonymous B fun h => do
        let rhs ← go t h
        let rhs_lam ← Meta.mkLambdaFVars #[h] rhs
        Meta.mkAppM `Or.elim #[or_pf, e, rhs_lam]
    | _ => throwError ""

namespace foo

syntax (name := univ_cad) "univ_cad" term "," term "," ("[" term,* "]") : tactic

-- Nat for now because its easier, later we have to instrument lean-smt to parse algebraic numbers to real numbers
def parseUnivCad : Syntax → TacticM (Expr × Expr × List Expr)
  | `(tactic| univ_cad $x, $h, [ $[$as],* ]) => do
      let as ← as.toList.mapM (elabTerm · none)
      let x' ← elabTerm x none
      let h' ← elabTerm h none
      return (x', h', as)
  | _ => throwError "[univ_cad]: wrong usage"

/- @[tactic univ_cad] def evalUnivCad : Tactic := fun stx => withMainContext do -/
/-   let (x, h, roots) ← parseUnivCad stx -/
/-   let roots_sorted_pf ← genPfSortedLT roots -/
/-   let decompPf ← getDecompPf x roots roots_sorted_pf h -/
/-   let decompType ← Meta.inferType decompPf -/
/-   let mainMv ← getMainGoal -/
/-   let (fv_decomp, mainMv) ← MVarId.intro1P $ ← mainMv.assert .anonymous decompType decompPf -/
/-   let ctx ← Meta.Simp.Context.mkDefault -/
/-   -- simp on the decomp hypothesis so it becomes a finite disjunction instead of an existential -/
/-   let (some (fv_decomp, mainMv), _) ← Lean.Meta.simpLocalDecl mainMv fv_decomp ctx | throwError "impossible" -/
/-   mainMv.withContext do -/
/-     let t ← fv_decomp.getType -/
/-     let disjuncts := collectDisjuncts t -/
/-     let disjunctsToFalse ← disjuncts.mapM (mkArrow · q(False)) -/
/-     let disjunctsToFalseMvs ← disjunctsToFalse.mapM (fun e => Meta.mkFreshExprMVar e) -/
/-     let answer ← go disjunctsToFalseMvs (.fvar fv_decomp) -/
/-     mainMv.assign answer -/
/-     let indexedGoals := disjunctsToFalseMvs.zipIdx -/
/-     let unsolvedMvs ← indexedGoals.mapM (fun (e, i) => solveCase e.mvarId! i) -/
/-     let unsolvedMvs := unsolvedMvs.foldr (fun o acc => match o with | some x => x :: acc | _ => acc) [] -/
/-     replaceMainGoal unsolvedMvs -/

/- open CompPoly -/

/- open CPolynomial in -/
/- def p1 : CPolynomial Rat := X^2 / 2 - 1 -/
/- open CPolynomial in -/
/- def p2 : CPolynomial Rat := X + 3 -/

/- def r1 : Raw := ⟨p2, -10, 0⟩ -/
/- def R1 : AlgNum := by lift_alg_num r1 -/

/- def r2 : Raw := ⟨p1, -2, -1⟩ -/
/- def R2 : AlgNum := by lift_alg_num r2 -/

/- def r3 : Raw := ⟨p1, 1, 2⟩ -/
/- def R3 : AlgNum := by lift_alg_num r3 -/


/- example (x : Real) (h : x + 3 < 0 ∧ (1/2) * x ^ 2 - 1 < 0) : False := by -/
/-   /1- have := in_component_prop (P := fun y => y + 3 < 0 ∧ (1/2) * y ^ 2 - 1 < 0) [1, 3, 4] (by grind) (by grind) x h -1/ -/
/-   univ_cad x, h, [R1, R2, R3] -/
/-   · admit -/
/-   · rintro ⟨h1, h2⟩ -/
/-     have := set_eq _ _ h1 -/
/-     rw [this] at h2 -/
/-     admit -/
/-   · admit -/
/-   · admit -/
/-   · admit -/
/-   · admit -/
/-   · admit -/

end foo
