import Smt.Reconstruct.Real.CAD.Sturm.Decidable

/-!
# Sturm sequences from certificates

The Sturm sequences of the reconstruction (`sturmSeqC'`) are computed by exact Euclidean division
over `ℚ`. cvc5 ships the sequences it computes over `ℤ` (by pseudo-division, dividing out the
content of each remainder): each element is the exact one multiplied by a constant, and comes with
the pseudo-quotient of the division that produced it. `certOk` checks such a sequence with
multiplications only, and `seqVarSturmC_ab'_eq_of_certOk` shows that its sign variations are those
of `sturmSeqC'`: every element is a constant multiple of the exact one, with constants of the same
sign. The constants themselves are not part of the certificate.
-/

open CompPoly Polynomial

namespace SturmCert

theorem toPoly_inj {f g : CPolynomial ℚ} (h : f.toPoly = g.toPoly) : f = g :=
  CPolynomial.eq_iff_coeff.mpr fun i => by rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, h]

theorem toPoly_C_mul (c : ℚ) (f : CPolynomial ℚ) :
    (CPolynomial.C c * f).toPoly = C c * f.toPoly := by
  rw [CPolynomial.toPoly_mul, CPolynomial.C_toPoly]

/-- Division with remainder is unique. -/
theorem mod_eq_of_eq_mul_add {f g q r : ℚ[X]} (h : f = q * g + r) (hr : r.degree < g.degree) :
    f % g = r := by
  have hg : g ≠ 0 := by
    rintro rfl
    simp at hr
  have hdvd : g ∣ f % g - r := ⟨q - f / g, by
    have := EuclideanDomain.div_add_mod f g
    linear_combination this + h⟩
  have hdeg : (f % g - r).degree < g.degree :=
    lt_of_le_of_lt (degree_sub_le _ _) (max_lt (degree_mod_lt f hg) hr)
  exact sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt hdvd hdeg)

theorem pos_mul_of_same_sign {ε a b : ℚ} (ha : 0 < ε * a) (hb : 0 < ε * b) : 0 < a * b := by
  nlinarith [mul_pos ha hb, sq_nonneg ε]

/-- The polynomial with the coefficients `cs`, lowest degree first. The shipped Sturm sequences are
stated this way: the kernel then reads their coefficients, instead of building each polynomial from
`C c * X ^ k` by polynomial arithmetic in every `decide`. -/
def ofCoeffs (cs : Array ℚ) : CPolynomial ℚ :=
  ⟨(CPolynomial.Raw.mk cs).trim, CPolynomial.Raw.Trim.trim_twice _⟩

/-! ### Sign variations under scaling -/

/-- `s` is `e` multiplied by a constant with the sign of `ε`. -/
def Scaled (ε : ℚ) (e s : CPolynomial ℚ) : Prop :=
  ∃ c : ℚ, 0 < ε * c ∧ s.toPoly = C c * e.toPoly

/-- `y` is `x` multiplied by a constant with the sign of `ε`. -/
def ScaledQ (ε : ℚ) (x y : ℚ) : Prop :=
  ∃ c : ℚ, 0 < ε * c ∧ y = c * x

theorem seqVarQ_aux_scaled {ε : ℚ} :
    ∀ {xs ys : List ℚ}, List.Forall₂ (ScaledQ ε) xs ys →
      ∀ {px py cp : ℚ}, 0 < ε * cp → py = cp * px → seqVarQ_aux px xs = seqVarQ_aux py ys := by
  intro xs ys h
  induction h with
  | nil => intros; simp [seqVarQ_aux]
  | @cons x y xs ys hxy _ ih =>
    intro px py cp hcp hp
    obtain ⟨c, hc, rfl⟩ := hxy
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    have hk : 0 < cp * c := pos_mul_of_same_sign hcp hc
    have hzero : (c * x == 0) = (x == 0) := by
      simp [hc0]
    have hsign : (py * (c * x) < 0) ↔ (px * x < 0) := by
      rw [hp, show cp * px * (c * x) = (cp * c) * (px * x) by ring]
      constructor
      · intro h; by_contra h'; push_neg at h'; nlinarith
      · intro h; nlinarith
    simp only [seqVarQ_aux, hzero]
    split
    · exact ih hcp hp
    · simp only [hsign]
      split
      · rw [ih hc rfl]
      · exact ih hc rfl

theorem seqVarQ'_scaled {ε : ℚ} {xs ys : List ℚ} (h : List.Forall₂ (ScaledQ ε) xs ys) :
    seqVarQ' xs = seqVarQ' ys := by
  cases h with
  | nil => rfl
  | cons hxy h =>
    obtain ⟨c, hc, rfl⟩ := hxy
    exact seqVarQ_aux_scaled h hc rfl

theorem seqEvalC_scaled {ε : ℚ} {L S : List (CPolynomial ℚ)} (h : List.Forall₂ (Scaled ε) L S)
    (x : ℚ) : List.Forall₂ (ScaledQ ε) (seqEvalC x L) (seqEvalC x S) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons e s _ _ hes _ ih =>
    obtain ⟨c, hc, hs⟩ := hes
    refine List.Forall₂.cons ⟨c, hc, ?_⟩ ih
    rw [CPolynomial.eval_toPoly, CPolynomial.eval_toPoly, hs, eval_mul, eval_C]

/-! ### The certificate -/

/-- The divisions after the first two elements `a`, `b`: for each further element `c`, a step
`(q, m, k)` with `m • a = q * b - k • c`, `deg c < deg b` and `m * k > 0`; that is, `c` is a constant
multiple of the negated remainder of `a` by `b`, with a positive factor. At the end `(q, m)` with
`m • a = q * b` for the last two elements: the remainder is zero. -/
def chainOk : CPolynomial ℚ → CPolynomial ℚ → List (CPolynomial ℚ) →
    List (CPolynomial ℚ × ℚ × ℚ) → CPolynomial ℚ × ℚ → Bool
  | a, b, [], [], (q, m) =>
    !decide (b = 0) && !decide (m = 0) && decide (CPolynomial.C m * a = q * b)
  | a, b, c :: S, (q, m, k) :: steps, fin =>
    decide (CPolynomial.C m * a = q * b - CPolynomial.C k * c) && !decide (c = 0) &&
      decide (c.natDegree < b.natDegree) && decide (0 < m * k) && chainOk b c S steps fin
  | _, _, _, _, _ => false

/-- `S0 :: S1 :: S` is the Sturm sequence of `(p, q)` up to constant factors: `S0 = c0 • p`,
`S1 = c1 • q` with `c0`, `c1` of the same sign, and the divisions check (`chainOk`). -/
def certOk (p q : CPolynomial ℚ) (c0 c1 : ℚ) (S0 S1 : CPolynomial ℚ) (S : List (CPolynomial ℚ))
    (steps : List (CPolynomial ℚ × ℚ × ℚ)) (fin : CPolynomial ℚ × ℚ) : Bool :=
  !decide (S0 = 0) && decide (S0 = CPolynomial.C c0 * p) && decide (S1 = CPolynomial.C c1 * q) &&
    decide (0 < c0 * c1) && chainOk S0 S1 S steps fin

theorem ne_zero_of_scaled {a e : CPolynomial ℚ} {c : ℚ} (h : a.toPoly = C c * e.toPoly)
    (ha : a ≠ 0) : e ≠ 0 := by
  rintro rfl
  apply ha
  apply poly_eq0_of_toPoly_eq0
  rw [h, CPolynomial.toPoly_zero, mul_zero]

theorem chainOk_sound (ε : ℚ) (fin : CPolynomial ℚ × ℚ) :
    ∀ (S : List (CPolynomial ℚ)) (steps : List (CPolynomial ℚ × ℚ × ℚ)) (a b ea eb : CPolynomial ℚ)
      (ca cb : ℚ), 0 < ε * ca → 0 < ε * cb → a.toPoly = C ca * ea.toPoly →
      b.toPoly = C cb * eb.toPoly → a ≠ 0 → chainOk a b S steps fin = true →
      List.Forall₂ (Scaled ε) (sturmSeqC ea eb) (a :: b :: S) := by
  intro S
  induction S with
  | nil =>
    intro steps a b ea eb ca cb hca hcb hA hB ha h
    obtain ⟨q, m⟩ := fin
    cases steps with
    | cons _ _ => simp [chainOk] at h
    | nil =>
      simp only [chainOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq] at h
      obtain ⟨⟨hb, hm⟩, hid⟩ := h
      have hca0 : ca ≠ 0 := by rintro rfl; simp at hca
      have hea : ea ≠ 0 := ne_zero_of_scaled hA ha
      have heb : eb ≠ 0 := ne_zero_of_scaled hB hb
      have hid' := congrArg CPolynomial.toPoly hid
      rw [toPoly_C_mul, CPolynomial.toPoly_mul] at hid'
      -- `eb` divides `ea`, so the next remainder is zero
      have hdvd : eb.toPoly ∣ -ea.toPoly := by
        refine ⟨-(C (ca⁻¹ * m⁻¹ * cb) * q.toPoly), ?_⟩
        have hEA : ea.toPoly = C ca⁻¹ * a.toPoly := by
          rw [hA, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hca0, C_1, one_mul]
        have hA' : a.toPoly = C m⁻¹ * (q.toPoly * b.toPoly) := by
          rw [← hid', ← mul_assoc, ← C_mul, inv_mul_cancel₀ hm, C_1, one_mul]
        rw [hEA, hA', hB]
        simp only [map_mul]
        ring
      have hrem : -ea % eb = 0 := by
        apply poly_eq0_of_toPoly_eq0
        rw [toPoly_mod, CPolynomial.toPoly_neg]
        exact EuclideanDomain.mod_eq_zero.mpr hdvd
      rw [sturmSeqC.eq_1, if_neg hea, hrem, sturmSeqC.eq_1, if_neg heb, sturmSeqC.eq_1, if_pos rfl]
      exact .cons ⟨ca, hca, hA⟩ (.cons ⟨cb, hcb, hB⟩ .nil)
  | cons c S ih =>
    intro steps a b ea eb ca cb hca hcb hA hB ha h
    cases steps with
    | nil => simp [chainOk] at h
    | cons st steps =>
      obtain ⟨q, m, k⟩ := st
      simp only [chainOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hid, hc⟩, hdeg⟩, hmk⟩, hrest⟩ := h
      have hca0 : ca ≠ 0 := by rintro rfl; simp at hca
      have hcb0 : cb ≠ 0 := by rintro rfl; simp at hcb
      have hm0 : m ≠ 0 := by rintro rfl; simp at hmk
      have hk0 : k ≠ 0 := by rintro rfl; simp at hmk
      have hb : b ≠ 0 := by
        rintro rfl
        rw [CPolynomial.natDegree_toPoly 0, CPolynomial.toPoly_zero, natDegree_zero] at hdeg
        exact Nat.not_lt_zero _ hdeg
      have hea : ea ≠ 0 := ne_zero_of_scaled hA ha
      have hid' := congrArg CPolynomial.toPoly hid
      rw [toPoly_C_mul, CPolynomial.toPoly_sub, CPolynomial.toPoly_mul, toPoly_C_mul] at hid'
      -- the exact remainder is a constant multiple of `c`
      set rc := ca⁻¹ * m⁻¹ * k with hrc
      have hrc0 : rc ≠ 0 := by simp [hrc, hca0, hm0, hk0]
      have hcP : c.toPoly ≠ 0 := toPoly_ne0_of_poly_ne0 c hc
      have hdegc : c.toPoly.degree < eb.toPoly.degree := by
        have hEB : eb.toPoly = C cb⁻¹ * b.toPoly := by
          rw [hB, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hcb0, C_1, one_mul]
        rw [hEB, degree_C_mul (inv_ne_zero hcb0)]
        apply degree_lt_degree
        rw [← CPolynomial.natDegree_toPoly, ← CPolynomial.natDegree_toPoly]
        exact hdeg
      have hmod : (-ea % eb).toPoly = C rc * c.toPoly := by
        rw [toPoly_mod, CPolynomial.toPoly_neg]
        apply mod_eq_of_eq_mul_add (q := -(C (ca⁻¹ * m⁻¹ * cb) * q.toPoly))
        · have hEA : ea.toPoly = C ca⁻¹ * a.toPoly := by
            rw [hA, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hca0, C_1, one_mul]
          have hA' : a.toPoly = C m⁻¹ * (q.toPoly * b.toPoly - C k * c.toPoly) := by
            rw [← hid', ← mul_assoc, ← C_mul, inv_mul_cancel₀ hm0, C_1, one_mul]
          rw [hEA, hA', hB, hrc]
          simp only [map_mul]
          ring
        · rw [degree_C_mul hrc0]
          exact hdegc
      have hC : c.toPoly = C rc⁻¹ * (-ea % eb).toPoly := by
        rw [hmod, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hrc0, C_1, one_mul]
      have hcc : 0 < ε * rc⁻¹ := by
        have : ε * rc⁻¹ = (ε * ca) * (m * k) / (k * k) := by
          rw [hrc]
          field_simp
        rw [this]
        exact div_pos (mul_pos hca hmk) (mul_self_pos.mpr hk0)
      rw [sturmSeqC.eq_1, if_neg hea]
      exact .cons ⟨ca, hca, hA⟩ (ih steps b c eb (-ea % eb) cb rc⁻¹ hcb hcc hB hC hb hrest)

theorem c0_ne_zero_of_certOk {p q : CPolynomial ℚ} {c0 c1 : ℚ} {S0 S1 : CPolynomial ℚ}
    {S : List (CPolynomial ℚ)} {steps : List (CPolynomial ℚ × ℚ × ℚ)} {fin : CPolynomial ℚ × ℚ}
    (h : certOk p q c0 c1 S0 S1 S steps fin = true) : c0 ≠ 0 := by
  simp only [certOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  rintro rfl
  simp at h

theorem sturmSeqC_scaled {p q : CPolynomial ℚ} {c0 c1 : ℚ} {S0 S1 : CPolynomial ℚ}
    {S : List (CPolynomial ℚ)} {steps : List (CPolynomial ℚ × ℚ × ℚ)} {fin : CPolynomial ℚ × ℚ}
    (h : certOk p q c0 c1 S0 S1 S steps fin = true) :
    List.Forall₂ (Scaled c0) (sturmSeqC p q) (S0 :: S1 :: S) := by
  have hc0 := c0_ne_zero_of_certOk h
  simp only [certOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hS0, h0⟩, h1⟩, hc01⟩, hchain⟩ := h
  have hA : S0.toPoly = C c0 * p.toPoly := by rw [h0, toPoly_C_mul]
  have hB : S1.toPoly = C c1 * q.toPoly := by rw [h1, toPoly_C_mul]
  exact chainOk_sound c0 fin S steps S0 S1 p q c0 c1 (mul_self_pos.mpr hc0) hc01 hA hB hS0 hchain

/-- The sign variations of a checked certificate are those of the Sturm sequence. -/
theorem seqVarSturmC_ab'_eq_of_certOk {p q : CPolynomial ℚ} {c0 c1 : ℚ} {S0 S1 : CPolynomial ℚ}
    {S : List (CPolynomial ℚ)} {steps : List (CPolynomial ℚ × ℚ × ℚ)} {fin : CPolynomial ℚ × ℚ}
    (h : certOk p q c0 c1 S0 S1 S steps fin = true) (a b : ℚ) :
    seqVarSturmC_ab' p q a b = seqVarQ_ab' (S0 :: S1 :: S) a b := by
  have hs := sturmSeqC_scaled h
  unfold seqVarSturmC_ab' seqVarQ_ab'
  rw [sturmSeqC_equiv, seqVarQ'_scaled (seqEvalC_scaled hs a),
    seqVarQ'_scaled (seqEvalC_scaled hs b)]

/-! ### Signs at infinity

The counts on half-lines and on the whole line also compare the signs of the sequence at `±∞`, that
is, of the leading coefficients (with the parity of the degree at `-∞`). Scaling an element by `c`
scales its leading coefficient by `c` and keeps its degree, so all signs at infinity are multiplied
by the common sign of the factors. -/

/-- `y` is `x` multiplied by an integer with the sign of `σ`. -/
def ScaledZ (σ : ℤ) (x y : ℤ) : Prop :=
  ∃ c : ℤ, 0 < σ * c ∧ y = c * x

theorem seqVarI_aux_scaled {σ : ℤ} :
    ∀ {xs ys : List ℤ}, List.Forall₂ (ScaledZ σ) xs ys →
      ∀ {px py cp : ℤ}, 0 < σ * cp → py = cp * px → seqVarI_aux px xs = seqVarI_aux py ys := by
  intro xs ys h
  induction h with
  | nil => intros; simp [seqVarI_aux]
  | @cons x y xs ys hxy _ ih =>
    intro px py cp hcp hp
    obtain ⟨c, hc, rfl⟩ := hxy
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    have hk : 0 < cp * c := by nlinarith [mul_pos hcp hc, sq_nonneg σ]
    have hzero : (c * x == 0) = (x == 0) := by
      simp [hc0]
    have hsign : (py * (c * x) < 0) ↔ (px * x < 0) := by
      rw [hp, show cp * px * (c * x) = (cp * c) * (px * x) by ring]
      constructor
      · intro h; by_contra h'; push_neg at h'; nlinarith
      · intro h; nlinarith
    simp only [seqVarI_aux, hzero]
    split
    · exact ih hcp hp
    · simp only [hsign]
      split
      · rw [ih hc rfl]
      · exact ih hc rfl

theorem seqVarI'_scaled {σ : ℤ} {xs ys : List ℤ} (h : List.Forall₂ (ScaledZ σ) xs ys) :
    seqVarI' xs = seqVarI' ys := by
  cases h with
  | nil => rfl
  | cons hxy h =>
    obtain ⟨c, hc, rfl⟩ := hxy
    exact seqVarI_aux_scaled h hc rfl

theorem sgnC_mul (a b : ℚ) : sgnC (a * b) = sgnC a * sgnC b := by
  rcases lt_trichotomy a 0 with ha | rfl | ha <;> rcases lt_trichotomy b 0 with hb | rfl | hb
  · have h : 0 < a * b := mul_pos_of_neg_of_neg ha hb
    simp [sgnC, ha, hb, not_lt.mpr h.le, h.ne']
  · simp [sgnC]
  · have h : a * b < 0 := mul_neg_of_neg_of_pos ha hb
    simp [sgnC, ha, h, not_lt.mpr hb.le, hb.ne']
  · simp [sgnC]
  · simp [sgnC]
  · simp [sgnC]
  · have h : a * b < 0 := mul_neg_of_pos_of_neg ha hb
    simp [sgnC, h, hb, not_lt.mpr ha.le, ha.ne']
  · simp [sgnC]
  · have h : 0 < a * b := mul_pos ha hb
    simp [sgnC, not_lt.mpr ha.le, ha.ne', not_lt.mpr hb.le, hb.ne', not_lt.mpr h.le, h.ne']

theorem sgnC_pos_mul {ε c : ℚ} (h : 0 < ε * c) : 0 < sgnC ε * sgnC c := by
  rw [← sgnC_mul]
  simp [sgnC, not_lt.mpr h.le, h.ne']

theorem scaled_leadingCoeff {e s : CPolynomial ℚ} {c : ℚ} (h : s.toPoly = C c * e.toPoly) :
    s.leadingCoeff = c * e.leadingCoeff := by
  rw [CPolynomial.leadingCoeff_toPoly, CPolynomial.leadingCoeff_toPoly, h, leadingCoeff_mul,
    leadingCoeff_C]

theorem scaled_natDegree {e s : CPolynomial ℚ} {c : ℚ} (hc : c ≠ 0)
    (h : s.toPoly = C c * e.toPoly) : s.natDegree = e.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly, h, natDegree_C_mul hc]

theorem seq_sgn_pos_inf_scaled {ε : ℚ} {L S : List (CPolynomial ℚ)}
    (h : List.Forall₂ (Scaled ε) L S) :
    List.Forall₂ (ScaledZ (sgnC ε)) (seq_sgn_pos_inf'' L) (seq_sgn_pos_inf'' S) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons e s _ _ hes _ ih =>
    obtain ⟨c, hc, hs⟩ := hes
    refine List.Forall₂.cons ⟨sgnC c, sgnC_pos_mul hc, ?_⟩ ih
    simp only [sgn_pos_inf'']
    rw [scaled_leadingCoeff hs, sgnC_mul]

theorem seq_sgn_neg_inf_scaled {ε : ℚ} {L S : List (CPolynomial ℚ)}
    (h : List.Forall₂ (Scaled ε) L S) :
    List.Forall₂ (ScaledZ (sgnC ε)) (seq_sgn_neg_inf'' L) (seq_sgn_neg_inf'' S) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons e s _ _ hes _ ih =>
    obtain ⟨c, hc, hs⟩ := hes
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    refine List.Forall₂.cons ⟨sgnC c, sgnC_pos_mul hc, ?_⟩ ih
    simp only [sgn_neg_inf'']
    rw [scaled_natDegree hc0 hs, scaled_leadingCoeff hs, sgnC_mul]
    split <;> ring

/-- `seqVarAboveSturmC'`, on a given sequence. -/
def seqVarAboveC_a' (P : List (CPolynomial ℚ)) (a : ℚ) : ℤ :=
  (seqVarQ' (seqEvalC a P) : Int) - seqVarI' (seq_sgn_pos_inf'' P)

/-- `seqVarBelowSturmC'`, on a given sequence. -/
def seqVarBelowC_b' (P : List (CPolynomial ℚ)) (b : ℚ) : ℤ :=
  (seqVarI' (seq_sgn_neg_inf'' P) : Int) - seqVarQ' (seqEvalC b P)

theorem seqVarAboveSturmC'_eq_of_certOk {p q : CPolynomial ℚ} {c0 c1 : ℚ}
    {S0 S1 : CPolynomial ℚ} {S : List (CPolynomial ℚ)} {steps : List (CPolynomial ℚ × ℚ × ℚ)}
    {fin : CPolynomial ℚ × ℚ} (h : certOk p q c0 c1 S0 S1 S steps fin = true) (a : ℚ) :
    seqVarAboveSturmC' p q a = seqVarAboveC_a' (S0 :: S1 :: S) a := by
  have hs := sturmSeqC_scaled h
  unfold seqVarAboveSturmC' seqVarAboveC_a'
  rw [sturmSeqC_equiv, seqVarQ'_scaled (seqEvalC_scaled hs a),
    seqVarI'_scaled (seq_sgn_pos_inf_scaled hs)]

theorem seqVarBelowSturmC'_eq_of_certOk {p q : CPolynomial ℚ} {c0 c1 : ℚ}
    {S0 S1 : CPolynomial ℚ} {S : List (CPolynomial ℚ)} {steps : List (CPolynomial ℚ × ℚ × ℚ)}
    {fin : CPolynomial ℚ × ℚ} (h : certOk p q c0 c1 S0 S1 S steps fin = true) (b : ℚ) :
    seqVarBelowSturmC' p q b = seqVarBelowC_b' (S0 :: S1 :: S) b := by
  have hs := sturmSeqC_scaled h
  unfold seqVarBelowSturmC' seqVarBelowC_b'
  rw [sturmSeqC_equiv, seqVarQ'_scaled (seqEvalC_scaled hs b),
    seqVarI'_scaled (seq_sgn_neg_inf_scaled hs)]

theorem seqVarLineSturmC'_eq_of_certOk {p q : CPolynomial ℚ} {c0 c1 : ℚ}
    {S0 S1 : CPolynomial ℚ} {S : List (CPolynomial ℚ)} {steps : List (CPolynomial ℚ × ℚ × ℚ)}
    {fin : CPolynomial ℚ × ℚ} (h : certOk p q c0 c1 S0 S1 S steps fin = true) :
    seqVarLineSturmC' p q = seqVarLineC' (S0 :: S1 :: S) := by
  have hs := sturmSeqC_scaled h
  unfold seqVarLineSturmC' seqVarLineC'
  rw [sturmSeqC_equiv, seqVarI'_scaled (seq_sgn_neg_inf_scaled hs),
    seqVarI'_scaled (seq_sgn_pos_inf_scaled hs)]

namespace tests

-- p = x³ - 3x + 1; libpoly's sequence: p, x² - 1 (p'/3), 2x - 1, 1, with the pseudo-quotients
-- x (1·p = x·(x² - 1) - 1·(2x - 1)) and 2x + 1 (4·(x² - 1) = (2x + 1)·(2x - 1) - 3·1)
abbrev X' : CPolynomial ℚ := CPolynomial.X
abbrev C' (c : ℚ) : CPolynomial ℚ := CPolynomial.C c

def p : CPolynomial ℚ := X' ^ 3 - C' 3 * X' + C' 1

-- the coefficient-array form is the same polynomial (trailing zeros are trimmed)
example : ofCoeffs #[1, -3, 0, 1, 0] = p := by decide +kernel

theorem cert_p : certOk p (CPolynomial.derivative p) 1 (1/3) p (X' ^ 2 - C' 1)
    [C' 2 * X' - C' 1, C' 1] [(X', 1, 1), (C' 2 * X' + C' 1, 4, 3)] (C' 2 * X' - C' 1, 1) = true := by
  decide +kernel

-- the roots of p are about -1.88, 0.35 and 1.53; all counts are taken on the certificate
example : seqVarSturmC_ab' p (CPolynomial.derivative p) 0 1 = 1 := by
  rw [seqVarSturmC_ab'_eq_of_certOk cert_p]; decide +kernel

example : seqVarAboveSturmC' p (CPolynomial.derivative p) 0 = 2 := by
  rw [seqVarAboveSturmC'_eq_of_certOk cert_p]; decide +kernel

example : seqVarBelowSturmC' p (CPolynomial.derivative p) 0 = 1 := by
  rw [seqVarBelowSturmC'_eq_of_certOk cert_p]; decide +kernel

example : seqVarLineSturmC' p (CPolynomial.derivative p) = 3 := by
  rw [seqVarLineSturmC'_eq_of_certOk cert_p]; decide +kernel

end tests

end SturmCert
