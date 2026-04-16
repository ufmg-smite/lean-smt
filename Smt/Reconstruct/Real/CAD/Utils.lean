import Mathlib
import Lean
import CompPoly

open Lean Elab Tactic ToExpr Meta

def normNum (mv : MVarId) : MetaM Unit := do
  let simpTheorems : Meta.SimpTheorems ← Meta.getSimpTheorems
  let ctx ← Meta.Simp.mkContext (simpTheorems := #[simpTheorems])
  let remainingGoal? ← (Mathlib.Tactic.transformAtTarget (fun e ctx ↦ Mathlib.Meta.NormNum.deriveSimp ctx (useSimp := true) e) "norm_num" (failIfUnchanged := false) mv).run ctx
  match remainingGoal? with
  | .some _ => throwError "[norm_num]: could not prove {← mv.getType}"
  | .none => pure ()

def runGrind (mv : MVarId) : MetaM Bool := do
  let params ← Meta.Grind.mkDefaultParams {}
  let r ← Meta.Grind.main mv params
  return !r.hasFailed

-- runGrind with a set of extra hypothesis
def runGrind' (mv : MVarId) (pfs : List Expr) : MetaM Bool := do
  let mut mv := mv
  for pf in pfs do
    let t ← inferType pf
    let (_, mv') ← MVarId.intro1P $ ← mv.assert .anonymous t pf
    mv := mv'
  let params ← Meta.Grind.mkDefaultParams {}
  let r ← Meta.Grind.main mv params
  return !r.hasFailed

def simp' (mvarId : MVarId) (hs : List Expr) (to_erase: List Name := []) : MetaM (Option MVarId) := mvarId.withContext do
  let congrTheorems ← getSimpCongrTheorems
  let mut simpTheorems ← getSimpTheorems
  for h in to_erase do
    simpTheorems := SimpTheorems.eraseCore simpTheorems (.decl h)
  let mut simpTheoremsArray : SimpTheoremsArray := #[simpTheorems]
  for h in hs do
    simpTheoremsArray ← SimpTheoremsArray.addTheorem simpTheoremsArray (.other `h) h
  let simprocs ← Simp.getSimprocs
  let ctx ← Simp.mkContext (simpTheorems := simpTheoremsArray) (congrTheorems := congrTheorems)
  let (result?, _) ← simpTarget mvarId ctx (simprocs := #[simprocs])
  return result?

def rewriteMVar (mvarId : MVarId) (eqProof : Expr) : MetaM MVarId :=
  mvarId.withContext do
    let tgt    ← mvarId.getType
    let result ← mvarId.rewrite tgt eqProof
    let newMVar ← mkFreshExprSyntheticOpaqueMVar result.eNew
    mvarId.assign (← mkEqMPR result.eqProof newMVar)
    return newMVar.mvarId!

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
  let h1'Type ← inferType h1'
  unless ← isDefEq h1'Type newProp do
    throwError "rewriteWithEq: type mismatch, expected {newProp} but got {h1'Type}"
  return h1'

noncomputable def sgn (k : ℝ) : ℤ  :=
  if k > 0 then 1
  else if k = 0 then 0
  else -1

lemma sgn_sgn_neg : ∀ x : ℝ, sgn x < 0 ↔ x < 0 := by
  intro x
  unfold sgn
  split_ifs
  next h =>
    simp only [Int.reduceLT, false_iff, not_lt]
    exact le_of_lt h
  next h1 h2 => simp [h2]
  next h1 h2 =>
    simp only [Int.reduceNeg, Left.neg_neg_iff, zero_lt_one, true_iff]
    push_neg at h1 h2
    exact lt_of_le_of_ne h1 h2

lemma sgn_sgn_zero : ∀ x : ℝ, sgn x = 0 ↔ x = 0 := by
  intro x
  unfold sgn
  split_ifs
  next h => simp only [one_ne_zero, false_iff]; exact ne_of_gt h
  next h => simp [h]
  next h1 h2 => simp [h2]

lemma sgn_sgn_pos : ∀ x : ℝ, sgn x > 0 ↔ x > 0 := by
  intro x
  unfold sgn
  split_ifs
  next h => simp [h]
  next h1 h2 => simp [h2]
  next h1 h2 => simp [h1]

lemma list_eq_of_sorted_of_length_of_mem (l1 l2 : List Real) : l1.length = l2.length → (∀ i ∈ l1, i ∈ l2) → l1.SortedLT → l2.SortedLT → l1 = l2 := by
  intros hlen h1 h2 h3
  have nd1 := h2.nodup
  have nd2 := h3.nodup
  have hcard : l1.toFinset.card = l2.toFinset.card := by
    rw [List.toFinset_card_of_nodup nd1, List.toFinset_card_of_nodup nd2, hlen]
  have hsub : l1.toFinset ⊆ l2.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact h1 x hx
  have hfeq : l1.toFinset = l2.toFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard.ge
  have hperm := List.perm_of_nodup_nodup_toFinset_eq nd1 nd2 hfeq
  exact hperm.eq_of_sortedLE h2.sortedLE h3.sortedLE

theorem no_roots_before_first' (p : Polynomial ℝ) (hp : p ≠ 0) (l : List ℝ)
    (hl : p.roots.toFinset.sort ⊆ l) (hl_sorted : l.SortedLT):
    ¬∃ x : ℝ , x < l[0]! ∧ p.eval x = 0 := by
  rintro ⟨x, hx1, hx2⟩
  have hx_l : x ∈ l := by
    apply hl
    simp [Finset.mem_sort, Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot]
    exact hx2
  obtain ⟨j, hj_bound, hj_eq⟩ := List.getElem_of_mem hx_l
  have : l[0] > l[j] := by
    rw [hj_eq]
    grind
  have : l[0] ≤ l[j] := by
    apply (StrictMono.le_iff_le hl_sorted).mpr
    exact left_eq_inf.mp rfl
  linarith

theorem no_roots_before_first'' (p : Polynomial ℝ) (hp : p ≠ 0) (l l' : List ℝ)
    (hl' : l' = p.roots.toFinset.sort) (hl : l' ⊆ l) (hl_sorted : l.SortedLT) :
    ∀ x : ℝ , x < l[0]! → p.eval x ≠ 0 := by
  subst hl'
  have := no_roots_before_first' p hp l hl hl_sorted
  push_neg at this
  exact this

theorem no_roots_after_last' (p : Polynomial ℝ) (hp : p ≠ 0) (l : List ℝ)
    (hl : p.roots.toFinset.sort ⊆ l) (hl_sorted : l.SortedLT) :
    ¬ ∃ x : ℝ, l.getLast! < x ∧ p.eval x = 0 := by
  rintro ⟨x, hx1, hx2⟩
  have hx_l : x ∈ l := by
    apply hl
    simp [Finset.mem_sort, Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot]
    exact hx2
  obtain ⟨j, hj_bound, hj_eq⟩ := List.getElem_of_mem hx_l
  have : l.getLast! < l[j] := by
    rw [hj_eq]
    grind
  have : l[j] ≤ l.getLast! := by
    have : l.getLast! = l[l.length - 1] := by grind
    rw [this]
    apply (StrictMono.le_iff_le hl_sorted).mpr
    grind
  linarith

theorem no_roots_after_last'' (p : Polynomial ℝ) (hp : p ≠ 0) (l l' : List ℝ)
    (hl' : l' = p.roots.toFinset.sort) (hl : l' ⊆ l) (hl_sorted : l.SortedLT) :
    ∀ x : ℝ, l.getLast! < x → p.eval x ≠ 0 := by
  subst hl'
  have := no_roots_after_last' p hp l hl hl_sorted
  push_neg at this
  exact this

theorem no_roots_between_roots' (p : Polynomial ℝ) (hp : p ≠ 0) (l : List ℝ)
    (hl : p.roots.toFinset.sort ⊆ l) (hl_sorted : l.SortedLT) :
    ∀ i < l.length - 1, ¬∃ x : ℝ , x ∈ Set.Ioo l[i]! l[i+1]! ∧ p.eval x = 0 := by
  intro i hi
  by_contra h
  obtain ⟨x, ⟨hxi, hxi1⟩, hx_root⟩ := h
  have hx_l : x ∈ l := by
    apply hl
    simp [Finset.mem_sort, Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot]
    exact hx_root
  obtain ⟨j, hj_bound, hj_eq⟩ := List.getElem_of_mem hx_l
  have hi_bound : i < l.length := by omega
  have hi1_bound : i + 1 < l.length := by omega
  rw [getElem!_pos l i hi_bound] at hxi
  rw [getElem!_pos l (i + 1) hi1_bound] at hxi1
  rw [← hj_eq] at hxi hxi1
  have hsorted := List.pairwise_iff_getElem.mp (List.sortedLT_iff_pairwise.mp hl_sorted)
  by_cases hij : i < j
  · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hij) with heq | hlt
    · subst heq; linarith
    · linarith [hsorted (i + 1) j hi1_bound hj_bound hlt]
  · push_neg at hij
    rcases Nat.eq_or_lt_of_le hij with heq | hlt
    · subst heq; linarith
    · linarith [hsorted j i hj_bound hi_bound hlt]

theorem no_roots_between_roots'' (p : Polynomial ℝ) (hp : p ≠ 0) (l l' : List ℝ)
  (hl' : l' = p.roots.toFinset.sort) (hl : l' ⊆ l) (hl_sorted : l.SortedLT) :
    ∀ i < l.length - 1,
    ∀ x : ℝ , x ∈ Set.Ioo l[i]! l[i+1]! → p.eval x ≠ 0 := by
  subst hl'
  have := no_roots_between_roots' p hp l hl hl_sorted
  push_neg at this
  exact this

-- Em um intervalo que o polinômio não tem raízes, se o sinal de um polinomio é positivo em um ponto do intervalo, então ele é sempre positivo
open Polynomial in
theorem sign_stops_pos (x : ℝ) (p : Polynomial ℝ) (a b : ℝ) (h_no_roots : ∀ k : ℝ, k ∈ Set.Ioo a b → ¬p.eval k = 0) :
    x ∈ Set.Ioo a b → (p.eval x > 0 → ∀ y : ℝ, y ∈ Set.Ioo a b → p.eval y > 0) := by
  intro h_interval hpos y hy
  by_contra hneg
  have hle : eval y p ≤ 0 := not_lt.mp hneg
  have hx_le : x ≤ y ∨ y ≤ x := le_total x y
  have zero_in_interval : 0 ∈ Set.Icc (eval y p) (eval x p) := ⟨hle, le_of_lt hpos⟩
  have ⟨c, hcIoo, hc⟩ : ∃ c ∈ Set.Ioo a b, eval c p = 0 := by
    rcases hx_le with hxy | hyx
    · have hcont2 : ContinuousOn (fun t => p.eval t) (Set.Icc x y) := (Polynomial.continuous p).continuousOn
      have ⟨c, hc_mem, hc_zero⟩ : 0 ∈ (fun t => eval t p) '' Set.Icc x y := by
        apply intermediate_value_Icc' hxy hcont2
        exact zero_in_interval
      simp at hc_zero
      have hcIoo : c ∈ Set.Ioo a b := by
        simp_all only [Set.mem_Ioo, gt_iff_lt, not_lt, Set.mem_Icc, true_and]
        apply And.intro <;> linarith
      use c
    · have hcont : ContinuousOn (fun t => p.eval t) (Set.Icc y x) := (Polynomial.continuous p).continuousOn
      have ⟨c, hc_mem, hc_zero⟩ : 0 ∈ (fun t => eval t p) '' Set.Icc y x:= by
        apply intermediate_value_Icc hyx hcont
        exact zero_in_interval
      simp at hc_zero
      have hcIoo : c ∈ Set.Ioo a b := by
        simp_all only [Set.mem_Ioo, gt_iff_lt, not_lt, Set.mem_Icc, true_and]
        apply And.intro <;> linarith
      use c
  simp_all

-- Em um intervalo que o polinômio não tem raízes, se o sinal de um polinomio é positivo em um ponto do intervalo, então ele é sempre positivo
open Polynomial in
theorem sign_stops_pos_pre (x : ℝ) (p : Polynomial ℝ) (a : ℝ) (h_no_roots : ∀ k : ℝ, k < a → ¬p.eval k = 0) :
    x < a → (p.eval x > 0 → ∀ y : ℝ, y < a → p.eval y > 0) := by
  intro h_interval hpos y hy
  by_contra hneg
  have hle : eval y p ≤ 0 := not_lt.mp hneg
  have hx_le : x ≤ y ∨ y ≤ x := le_total x y
  have zero_in_interval : 0 ∈ Set.Icc (eval y p) (eval x p) := ⟨hle, le_of_lt hpos⟩
  have ⟨c, hcIoo, hc⟩ : ∃ c < a, eval c p = 0 := by
    rcases hx_le with hxy | hyx
    · have hcont2 : ContinuousOn (fun t => p.eval t) (Set.Icc x y) := (Polynomial.continuous p).continuousOn
      have ⟨c, hc_mem, hc_zero⟩ : 0 ∈ (fun t => eval t p) '' Set.Icc x y := by
        apply intermediate_value_Icc' hxy hcont2
        exact zero_in_interval
      simp at hc_zero
      have hcIoo : c < a := by
        simp_all only [gt_iff_lt, not_lt, Set.mem_Icc, true_and]
        linarith
      use c
    · have hcont : ContinuousOn (fun t => p.eval t) (Set.Icc y x) := (Polynomial.continuous p).continuousOn
      have ⟨c, hc_mem, hc_zero⟩ : 0 ∈ (fun t => eval t p) '' Set.Icc y x:= by
        apply intermediate_value_Icc hyx hcont
        exact zero_in_interval
      simp at hc_zero
      have hcIoo : c < a := by
        simp_all only [gt_iff_lt, not_lt, Set.mem_Icc, true_and]
        linarith
      use c
  simp_all

-- Em um intervalo que o polinômio não tem raízes, se o sinal de um polinomio é positivo em um ponto do intervalo, então ele é sempre positivo
open Polynomial in
theorem sign_stops_pos_pos (x : ℝ) (p : Polynomial ℝ) (b : ℝ) (h_no_roots : ∀ k : ℝ, b < k → ¬p.eval k = 0) :
    b < x → (p.eval x > 0 → ∀ y : ℝ, b < y → p.eval y > 0) := by
  intro h_interval hpos y hy
  by_contra hneg
  have hle : eval y p ≤ 0 := not_lt.mp hneg
  have hx_le : x ≤ y ∨ y ≤ x := le_total x y
  have zero_in_interval : 0 ∈ Set.Icc (eval y p) (eval x p) := ⟨hle, le_of_lt hpos⟩
  have ⟨c, hcIoo, hc⟩ : ∃ c > b, eval c p = 0 := by
    rcases hx_le with hxy | hyx
    · have hcont2 : ContinuousOn (fun t => p.eval t) (Set.Icc x y) := (Polynomial.continuous p).continuousOn
      have ⟨c, hc_mem, hc_zero⟩ : 0 ∈ (fun t => eval t p) '' Set.Icc x y := by
        apply intermediate_value_Icc' hxy hcont2
        exact zero_in_interval
      simp at hc_zero
      have hcIoo : c > b := by
        simp_all only [gt_iff_lt, not_lt, Set.mem_Icc, true_and]
        linarith
      use c
    · have hcont : ContinuousOn (fun t => p.eval t) (Set.Icc y x) := (Polynomial.continuous p).continuousOn
      have ⟨c, hc_mem, hc_zero⟩ : 0 ∈ (fun t => eval t p) '' Set.Icc y x:= by
        apply intermediate_value_Icc hyx hcont
        exact zero_in_interval
      simp at hc_zero
      have hcIoo : c > b := by
        simp_all only [gt_iff_lt, not_lt, Set.mem_Icc, true_and]
        linarith
      use c
  simp_all

open Polynomial in
theorem sign_stops_neg (x : ℝ) (p : Polynomial ℝ) (a b : ℝ) (h_no_roots : ∀ k : ℝ, k ∈ Set.Ioo a b → ¬p.eval k = 0) :
    x ∈ Set.Ioo a b → (p.eval x < 0 → ∀ y : ℝ, y ∈ Set.Ioo a b → p.eval y < 0) := by
  intro h_interval hneg y hy
  by_contra hpos
  have hle : eval y p ≥ 0 := not_lt.mp hpos
  have hx_le : x ≤ y ∨ y ≤ x := le_total x y
  have zero_in_interval : 0 ∈ Set.Icc (eval x p) (eval y p) := ⟨le_of_lt hneg, hle⟩
  have ⟨c, hcIoo, hc⟩ : ∃ c ∈ Set.Ioo a b, eval c p = 0 := by
    rcases hx_le with hxy | hyx
    · have hcont2 : ContinuousOn (fun t => p.eval t) (Set.Icc x y) := (Polynomial.continuous p).continuousOn
      have ⟨c, hc_mem, hc_zero⟩ : 0 ∈ (fun t => eval t p) '' Set.Icc x y := by
        apply intermediate_value_Icc hxy hcont2
        exact zero_in_interval
      simp at hc_zero
      have hcIoo : c ∈ Set.Ioo a b := by
        simp_all only [Set.mem_Ioo, not_lt, Set.mem_Icc]
        apply And.intro <;> linarith
      use c
    · have hcont : ContinuousOn (fun t => p.eval t) (Set.Icc y x) := (Polynomial.continuous p).continuousOn
      have ⟨c, hc_mem, hc_zero⟩ : 0 ∈ (fun t => eval t p) '' Set.Icc y x:= by
        apply intermediate_value_Icc' hyx hcont
        exact zero_in_interval
      simp at hc_zero
      have hcIoo : c ∈ Set.Ioo a b := by
        simp_all only [Set.mem_Ioo, not_lt, Set.mem_Icc]
        apply And.intro <;> linarith
      use c
  simp_all

-- Em um intervalo que o polinômio não tem raízes, se o sinal de um polinomio é positivo em um ponto do intervalo, então ele é sempre positivo
open Polynomial in
theorem sign_stops_neg_pre (x : ℝ) (p : Polynomial ℝ) (a : ℝ) (h_no_roots : ∀ k : ℝ, k < a → ¬p.eval k = 0) :
    x < a → (p.eval x < 0 → ∀ y : ℝ, y < a → p.eval y < 0) := by
  intro h_interval hpos y hy
  by_contra hneg
  have hle : eval y p ≥ 0 := not_lt.mp hneg
  have hx_le : x ≤ y ∨ y ≤ x := le_total x y
  have zero_in_interval : 0 ∈ Set.Icc (eval x p) (eval y p) := ⟨le_of_lt hpos, hle⟩
  have ⟨c, hcIoo, hc⟩ : ∃ c < a, eval c p = 0 := by
    rcases hx_le with hxy | hyx
    · have hcont2 : ContinuousOn (fun t => p.eval t) (Set.Icc x y) := (Polynomial.continuous p).continuousOn
      have ⟨c, hc_mem, hc_zero⟩ : 0 ∈ (fun t => eval t p) '' Set.Icc x y := by
        apply intermediate_value_Icc hxy hcont2
        exact zero_in_interval
      simp at hc_zero
      have hcIoo : c < a := by
        simp_all only [not_lt, Set.mem_Icc]
        linarith
      use c
    · have hcont : ContinuousOn (fun t => p.eval t) (Set.Icc y x) := (Polynomial.continuous p).continuousOn
      have ⟨c, hc_mem, hc_zero⟩ : 0 ∈ (fun t => eval t p) '' Set.Icc y x:= by
        apply intermediate_value_Icc' hyx hcont
        exact zero_in_interval
      simp at hc_zero
      have hcIoo : c < a := by
        simp_all only [not_lt, Set.mem_Icc]
        linarith
      use c
  simp_all

-- Em um intervalo que o polinômio não tem raízes, se o sinal de um polinomio é positivo em um ponto do intervalo, então ele é sempre positivo
open Polynomial in
theorem sign_stops_neg_pos (x : ℝ) (p : Polynomial ℝ) (b : ℝ) (h_no_roots : ∀ k : ℝ, b < k → ¬p.eval k = 0) :
    b < x → (p.eval x < 0 → ∀ y : ℝ, b < y → p.eval y < 0) := by
  intro h_interval hpos y hy
  by_contra hneg
  have hle : eval y p ≥ 0 := not_lt.mp hneg
  have hx_le : x ≤ y ∨ y ≤ x := le_total x y
  have zero_in_interval : 0 ∈ Set.Icc (eval x p) (eval y p) := ⟨le_of_lt hpos, hle⟩
  have ⟨c, hcIoo, hc⟩ : ∃ c > b, eval c p = 0 := by
    rcases hx_le with hxy | hyx
    · have hcont2 : ContinuousOn (fun t => p.eval t) (Set.Icc x y) := (Polynomial.continuous p).continuousOn
      have ⟨c, hc_mem, hc_zero⟩ : 0 ∈ (fun t => eval t p) '' Set.Icc x y := by
        apply intermediate_value_Icc hxy hcont2
        exact zero_in_interval
      simp at hc_zero
      have hcIoo : c > b := by
        simp_all only [not_lt, Set.mem_Icc]
        linarith
      use c
    · have hcont : ContinuousOn (fun t => p.eval t) (Set.Icc y x) := (Polynomial.continuous p).continuousOn
      have ⟨c, hc_mem, hc_zero⟩ : 0 ∈ (fun t => eval t p) '' Set.Icc y x:= by
        apply intermediate_value_Icc' hyx hcont
        exact zero_in_interval
      simp at hc_zero
      have hcIoo : c > b := by
        simp_all only [not_lt, Set.mem_Icc]
        linarith
      use c
  simp_all

open CompPoly

theorem gneg_imp_gtopoly_neg (g : CPolynomial ℚ) (h : g ≠ 0) : g.toPoly ≠ 0 := by
  intro abs
  have : g = 0 := by
    apply CPolynomial.eq_zero_iff_coeff_zero.mpr
    have aux (x : ℚ) := CPolynomial.eval_toPoly x g
    rw[abs] at aux
    simp at aux
    simp only [CPolynomial.coeff_toPoly]
    rw[abs]
    apply Polynomial.coeff_zero
  exact h this

theorem gtopolyzeroeq2 (g : CPolynomial ℚ) : g.toPoly ≠ 0 → g ≠ 0 := by
  contrapose
  intro h; rw[h]; exact CPolynomial.toPoly_zero

theorem gtopolyzeroeq (g : CPolynomial ℚ) : g.toPoly = 0 → g = 0 := by
  contrapose
  apply gneg_imp_gtopoly_neg

theorem fg_mod_eq (f g : CPolynomial ℚ) : (f % g).toPoly = f.toPoly % g.toPoly := by
  have aux := CPolynomial.mod_toPoly f g
  have : (f.mod g) = f%g := CPolynomial.eq_iff_coeff.mpr (congrFun rfl)
  rw[this] at aux
  apply aux

@[irreducible]
noncomputable def ratToRealHom : RingHom Rat Real := Rat.castHom Real

@[irreducible]
noncomputable def ratToReal : Rat → Real := ratToRealHom


@[grind =]
noncomputable def toPolyReal (p : CPolynomial Rat) : Polynomial Real := p.toPoly.map ratToRealHom

open CompPoly in
lemma toPolyReal_zero (p : CPolynomial Rat) : p ≠ 0 → toPolyReal p ≠ 0 := by
  intros h
  exact Polynomial.map_ne_zero (gneg_imp_gtopoly_neg p h)

theorem gneg_imp_gtopoly_neg' (g : CPolynomial ℚ) (h : g ≠ 0) : g.toPoly ≠ 0 := by
  intro abs
  have : g = 0 := by
    apply CPolynomial.eq_zero_iff_coeff_zero.mpr
    have aux (x : ℚ) := CPolynomial.eval_toPoly x g
    rw[abs] at aux
    simp at aux
    simp only [CPolynomial.coeff_toPoly]
    rw[abs]
    apply Polynomial.coeff_zero
  exact h this

theorem gtopolyzeroeq2' (g : CPolynomial ℚ) : g.toPoly ≠ 0 → g ≠ 0 := by
  contrapose
  intro h; rw[h]; exact CPolynomial.toPoly_zero

theorem gtopolyzeroeq' (g : CPolynomial ℚ) : g.toPoly = 0 → g = 0 := by
  contrapose
  apply gneg_imp_gtopoly_neg

