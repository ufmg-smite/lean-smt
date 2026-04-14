import Smt.Reconstruct.Real.CAD.Sturm.Theorem

open CompPoly

/-
Some definitions, such as `sturmSeqC` and `seqVarI`, even though are computable,
can't be reduced by `decide +kernel` (though they can be reduced by `native_decide`)
since they rely on non structural recursion, which is compiled to an application
of `WellFounded.fix`, which turns out to be noncomputable (I think it's weird that
we don't need to mark `sturmSeqC` and `seqVarI` as noncomputable in this case).
This file defines new versions of these functions without using nonstructural
recursion and prove their equivalence. In lean-smt we should use these versions
so we don't depend on `native_decide`.

TODO: We could erase the old definitions and just use these ones, but we will
have to reprove some theorems. I don't think it would make any difference on
performance.
-/

/-- Fuel-based version of `sturmSeqC` that uses structural recursion on a natural number,
    making it reducible by the kernel. -/
def sturmSeqC_fuel (fuel : ℕ) (f g : CPolynomial ℚ) : List (CPolynomial ℚ) :=
  if f = 0 then
    []
  else
    match fuel with
    | 0 => [f]
    | fuel + 1 => f :: sturmSeqC_fuel fuel g (-f % g)

/-- `sturmSeqC` with the default fuel based on `g.natDegree`. -/
def sturmSeqC' (f g : CPolynomial ℚ) : List (CPolynomial ℚ) :=
  sturmSeqC_fuel (g.natDegree + 2) f g

private theorem sturmSeqC_fuel_unfold (fuel : ℕ) (f g : CPolynomial ℚ) :
    sturmSeqC_fuel (fuel + 1) f g =
      if f = 0 then [] else f :: sturmSeqC_fuel fuel g (-f % g) := by
  simp [sturmSeqC_fuel]

private lemma sturmSeqC_fuel_zero (g : CPolynomial ℚ) (n : ℕ) :
    sturmSeqC_fuel n 0 g = [] := by
  cases n <;> simp [sturmSeqC_fuel]

theorem sturmSeqC_fuel_eq (f g : CPolynomial ℚ) (n : ℕ)
    (hn : n ≥ g.natDegree + 2) :
    sturmSeqC_fuel n f g = sturmSeqC f g := by
  induction n using Nat.strongRecOn generalizing f g with
  | ind n ih =>
    by_cases hf : f = 0
    · rw [hf, sturmSeqC_fuel_zero, sturmSeqC.eq_1]; simp
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [sturmSeqC_fuel_unfold, sturmSeqC.eq_1]; simp only [hf, ↓reduceIte]
      congr 1
      by_cases hg : g = 0
      · rw [hg, sturmSeqC_fuel_zero, sturmSeqC.eq_1]; simp
      · by_cases hmod : -f % g = 0
        · rw [hmod]
          have hseq : sturmSeqC g 0 = [g] := by
            rw [sturmSeqC.eq_1]; simp only [hg, ↓reduceIte]
            congr 1; rw [sturmSeqC.eq_1]; simp
          rw [hseq]
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
          rw [sturmSeqC_fuel_unfold]; simp only [hg, ↓reduceIte]
          congr 1; exact sturmSeqC_fuel_zero _ _
        · apply ih m (by omega)
          have hdeg : (-f % g).natDegree < g.natDegree := by
            rw [CPolynomial.natDegree_toPoly (-f % g), CPolynomial.natDegree_toPoly g]
            have htp : (-f % g).toPoly = (-f).toPoly % g.toPoly := fg_mod_eq (-f) g
            rw [htp, CPolynomial.toPoly_neg]
            apply Polynomial.natDegree_mod_lt
            intro h0
            apply hmod
            have hgp : g.toPoly ≠ 0 := gneg_imp_gtopoly_neg g hg
            have hnd : g.toPoly.natDegree = 0 := h0
            obtain ⟨c, hc⟩ : ∃ c : ℚ, Polynomial.C c = g.toPoly :=
              Polynomial.natDegree_eq_zero.mp hnd
            have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc; exact hgp hc.symm
            have hdvd : g.toPoly ∣ f.toPoly := by
              rw [← hc]
              exact IsUnit.dvd (Polynomial.isUnit_C.mpr (Ne.isUnit hc0))
            have h1 : (-f % g).toPoly = (-f).toPoly % g.toPoly := fg_mod_eq (-f) g
            rw [CPolynomial.toPoly_neg] at h1
            have h2 : -f.toPoly % g.toPoly = 0 := by
              rw [EuclideanDomain.mod_eq_zero]; exact dvd_neg.mpr hdvd
            exact gtopolyzeroeq (-f % g) (by rw [h1, h2])
          omega

theorem sturmSeqC_equiv (f g : CPolynomial ℚ) :
    sturmSeqC' f g = sturmSeqC f g := by
  unfold sturmSeqC'
  exact sturmSeqC_fuel_eq f g (g.natDegree + 2) (le_refl _)

def seqVarI_aux (prev : ℤ) : List ℤ → ℕ
  | [] => 0
  | b :: as =>
    if b == 0 then seqVarI_aux prev as
    else if prev * b < 0 then 1 + seqVarI_aux b as
    else seqVarI_aux b as

/-- Kernel-reducible version of `seqVarI`. -/
def seqVarI' : List ℤ → ℕ
  | [] => 0
  | a :: rest => seqVarI_aux a rest

theorem seqVarI_aux_eq_seqVarI (prev : ℤ) (rest : List ℤ) :
    seqVarI_aux prev rest = seqVarI (prev :: rest) := by
  induction rest generalizing prev with
  | nil => simp [seqVarI_aux, seqVarI.eq_2]
  | cons b as ih =>
    simp only [seqVarI_aux]
    rw [seqVarI.eq_3]
    split
    · rw [ih]
    · split
      · congr 1; rw [ih]
      · rw [ih]

theorem seqVarI_eq (l : List ℤ) : seqVarI' l = seqVarI l := by
  cases l with
  | nil => simp [seqVarI', seqVarI.eq_1]
  | cons a rest =>
    simp only [seqVarI']
    exact seqVarI_aux_eq_seqVarI a rest

def seqVarLineC' (P : List (CPolynomial ℚ)) : ℤ :=
  (seqVarI' (seq_sgn_neg_inf'' P) : Int) - seqVarI' (seq_sgn_pos_inf'' P)

theorem seqVarLine_eq (P : List (CPolynomial ℚ)) : seqVarLineC P = seqVarLineC' P := by
  unfold seqVarLineC seqVarLineC'
  rw [seqVarI_eq, seqVarI_eq]

def seqVarLineSturmC' (p q : CPolynomial ℚ) : ℤ :=
  seqVarLineC' (sturmSeqC' p q)

theorem seqVarLineSturmC_eq (p q : CPolynomial ℚ) : seqVarLineSturmC p q = seqVarLineSturmC' p q := by
  unfold seqVarLineSturmC seqVarLineSturmC'
  rw [seqVarLine_eq, sturmSeqC_equiv]

theorem seqVarLineEquivSturm' (p q : CPolynomial ℚ) : seqVarLineSturm (p.toPoly.map ratToRealHom) (q.toPoly.map ratToRealHom) = seqVarLineSturmC' p q  := by
  rw [<- seqVarLineSturmC_eq]
  exact (seqVarLineEquivSturm p q).symm

def seqVarQ_aux (prev : ℚ) : List ℚ → ℕ
  | [] => 0
  | b :: as =>
    if b == 0 then seqVarQ_aux prev as
    else if prev * b < 0 then 1 + seqVarQ_aux b as
    else seqVarQ_aux b as

/-- Kernel-reducible version of `seqVarI`. -/
def seqVarQ' : List ℚ → ℕ
  | [] => 0
  | a :: rest => seqVarQ_aux a rest

theorem seqVarQ_aux_eq_seqVarQ (prev : ℚ) (rest : List ℚ) :
    seqVarQ_aux prev rest = seqVarQ (prev :: rest) := by
  induction rest generalizing prev with
  | nil => simp [seqVarQ_aux, seqVarQ.eq_2]
  | cons b as ih =>
    simp only [seqVarQ_aux]
    rw [seqVarQ.eq_3]
    split
    · rw [ih]
    · split
      · congr 1; rw [ih]
      · rw [ih]

theorem seqVarQ_eq (l : List ℚ) : seqVarQ' l = seqVarQ l := by
  cases l with
  | nil => simp [seqVarQ', seqVarQ.eq_1]
  | cons a rest =>
    simp only [seqVarQ']
    exact seqVarQ_aux_eq_seqVarQ a rest

def seqVarQ_ab' (P: List (CPolynomial ℚ)) (a b: ℚ): ℤ :=
  (seqVarQ' (seqEvalC a P) : Int) - seqVarQ' (seqEvalC b P)

lemma seqVarQ_ab_equiv (P : List (CPolynomial ℚ)) (a b : ℚ) :
    seqVarQ_ab P a b = seqVarQ_ab' P a b := by
  unfold seqVarQ_ab seqVarQ_ab'
  rw [seqVarQ_eq, seqVarQ_eq]

def seqVarSturmC_ab' (p q: CPolynomial ℚ) (a b : ℚ) : ℤ :=
  seqVarQ_ab' (sturmSeqC' p q) a b

lemma seqVarSturmC_ab_equiv (p q : CPolynomial ℚ) (a b : ℚ) :
    seqVarSturmC_ab p q a b = seqVarSturmC_ab' p q a b := by
  unfold seqVarSturmC_ab' seqVarSturmC_ab
  rw [seqVarQ_ab_equiv, sturmSeqC_equiv]
