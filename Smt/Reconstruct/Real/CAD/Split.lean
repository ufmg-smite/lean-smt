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
    if first then {y | y < x} :: {y | y = x} :: {y | y > x} :: []
    else {y | y = x} :: {y | y > x} :: []
  | x :: y :: t =>
    if first then
      {z | z < x} :: {z | z = x} :: {z | z > x ∧ z < y} :: decomp' (y :: t) (by grind) false
    else
      {z | z = x} :: {z | z > x ∧ z < y} :: decomp' (y :: t) (by grind) false

@[simp]
def decomp (l : List ℝ) (sl : l.SortedLT) : List (Set ℝ) := decomp' l sl true

@[simp]
def decomp'_merge (l : List ℝ) (sl : l.SortedLT) : Set ℝ := (decomp' l sl false).foldr (fun s acc => s ∪ acc) ∅

@[simp]
def decomp_merge (l : List ℝ) (sl : l.SortedLT) : Set ℝ := (decomp l sl).foldr (fun s acc => s ∪ acc) ∅

lemma decomp'_covers (hd : ℝ) (tl : List ℝ) (sl : (hd :: tl).SortedLT) :
    decomp'_merge (hd :: tl) sl = {x | x ≥ hd} := by
  cases tl with
  | nil =>
    ext z
    simp only [decomp'_merge, decomp', Bool.false_eq_true, ↓reduceIte, List.foldr_cons,
      List.foldr_nil, Set.union_empty, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      rcases h.lt_or_eq with h | h
      · exact Or.inr h
      · exact Or.inl h.symm
  | cons hd' tl' =>
    have ih := decomp'_covers hd' tl' (by grind)
    have hlt : hd < hd' := by grind
    simp only [decomp'_merge] at ih
    ext z
    simp only [decomp'_merge, decomp', Bool.false_eq_true, ↓reduceIte, List.foldr_cons,
      Set.mem_union, Set.mem_ofPred_eq, ih]
    constructor
    · rintro (h | ⟨h, _⟩ | h) <;> linarith
    · intro h
      rcases h.lt_or_eq with h | h
      · rcases lt_or_ge z hd' with h' | h'
        · exact Or.inr (Or.inl ⟨h, h'⟩)
        · exact Or.inr (Or.inr h')
      · exact Or.inl h.symm

lemma decomp_covers (l : List ℝ) (sl : l.SortedLT) (hl : l ≠ []) :
    decomp_merge l sl = (Set.univ : Set ℝ) :=
  match l with
  | [] => absurd rfl hl
  | [x] => by
    ext z
    simp only [decomp_merge, decomp, decomp', ↓reduceIte, List.foldr_cons, List.foldr_nil,
      Set.union_empty, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    rcases lt_trichotomy z x with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  | x :: y :: t => by
    have hcov := decomp'_covers y t (by grind)
    have hxy : x < y := by grind
    simp only [decomp'_merge] at hcov
    ext z
    simp only [decomp_merge, decomp, decomp', ↓reduceIte, List.foldr_cons, Set.mem_union,
      Set.mem_ofPred_eq, Set.mem_univ, iff_true, hcov]
    rcases lt_trichotomy z x with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases lt_or_ge z y with h' | h'
      · exact Or.inr (Or.inr (Or.inl ⟨h, h'⟩))
      · exact Or.inr (Or.inr (Or.inr h'))

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
  -- `roots` is an explicit non-empty list literal
  let .app (.app (.app (.const ``List.cons _) _) hd) tl := roots
    | throwError "getDecompPf: expected a non-empty list literal, got {roots}"
  let roots_not_empty_pf ← Meta.mkAppM ``List.cons_ne_nil #[hd, tl]
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

end foo
