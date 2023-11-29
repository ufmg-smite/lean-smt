import Mathlib

def BitVec w := Fin (2 ^ w)




example {a b : Nat} (h : ¬ a < b) : b ≤ a := by library_search

theorem p_imp_q (hpq :   p → q ) :  ¬ q → ¬ p := fun hnq hp => hnq (hpq hp)

theorem p_imp_q_imp_r (h: p → q → r → s) : ¬ s → q ∧ r → ¬ p:= by
aesop





example (a b :ℕ) (h:  b <a ) (h1 : c < b) : Nat.succ c < a:= by library_search




theorem contra_le_of_testBit {n m :ℕ} (i :ℕ) (h: n ≤ m) :  Nat.testBit n i = true ∧ Nat.testBit m i = false → (∃ (j : ℕ), i < j ∧  Nat.testBit n j ≠ Nat.testBit m j) :=by
  have H := @Nat.lt_of_testBit m n i
  contrapose! H
  aesop

theorem most_sig_eq {n m :ℕ} (h : n ≠ m) : ∃ i, Nat.testBit n i ≠ Nat.testBit m i ∧ ∀ j > i, Nat.testBit n j = Nat.testBit m j := by
  have H2 : ¬(∀ (i : ℕ), Nat.testBit n i = Nat.testBit m i) := (fun hnq hp => hnq (Nat.eq_of_testBit_eq hp)) h
  push_neg at H2
  by_contra' H3
  replace H3 : ∀ i, Nat.testBit n i ≠ Nat.testBit m i → ∃ j, j>i ∧ Nat.testBit n j ≠ Nat.testBit m j := by aesop
  have ⟨k1, Hk1⟩:= Nat.exists_most_significant_bit (show n≠ 0 by sorry)
  have ⟨k2, Hk2⟩:= Nat.exists_most_significant_bit (show m≠ 0 by sorry)
  have ⟨u, hu⟩ := H2 
  let M := max k1 k2
  have H4 : ∀ i:ℕ, ∃ l, l>i ∧ Nat.testBit n l ≠ Nat.testBit m l := by
    intro i
    induction' i with d hd
    · have ⟨v, hv1, hv2⟩ := H3 u hu
      use v
      exact ⟨pos_of_gt hv1, hv2⟩ 
    · have ⟨l, hl1, hl2⟩ := hd
      have ⟨v, hv1, hv2⟩ := H3 l hl2
      use v
      exact ⟨ instTransGtToLTGeToLE.proof_1 hv1 hl1, hv2⟩ 
  have ⟨l, hl1, hl2⟩ := H4 M
  replace Hk1 := Hk1.right l (show k1 < l by aesop)
  replace Hk2 := Hk2.right l (show k2 < l by aesop)
  rw [← Hk1] at Hk2
  exact hl2 (Eq.symm Hk2)



  


theorem contra_lt_of_testBit' {n m :ℕ} (h: n < m) : ∃ i, Nat.testBit n i = false ∧ Nat.testBit m i = true ∧ (∀ (j : ℕ), i < j →  Nat.testBit n j = Nat.testBit m j) := by
  have H := @contra_le_of_testBit n m
  have ⟨i, hi1, hi2⟩ := most_sig_eq (Nat.ne_of_lt h)
  by_cases hni : Nat.testBit n i <;> by_cases hmi : Nat.testBit m i
  · simp [*] at *
  · replace hmi: Nat.testBit m i = false := by aesop
    have ⟨j,  hj1, hj2⟩ := H i (Nat.le_of_lt h)  ⟨hni, hmi⟩
    exfalso
    have hi3 := hi2 j (hj1)
    contradiction
  · use i
    exact ⟨ (show _ by simp [hni]), hmi, (show _ by aesop)⟩ 
  · simp [*] at *



theorem exists_most_significant_bit' {n : BitVec w} :
    ∀ i, Nat.testBit n.val i = true → i < w := by
    have ⟨n, hn⟩ := n
    intro i h
    replace h : Nat.testBit n i = true := h
    by_contra' h2
    replace h2 : w ≤ i := Nat.le_of_not_lt h2
    have ⟨k, hk, hj⟩ := Nat.exists_most_significant_bit (show n ≠ 0 by sorry) 
    have h3: i ≤ k:= by
      by_contra' h4
      have h5 := hj i h4
      rw [h] at h5
      contradiction
    have h8 := Nat.le_trans h2 h3
    have ⟨l, hl1, hl2, hl3⟩  := contra_lt_of_testBit' hn
    cases' Nat.eq_or_lt_of_le h8 with h9 h10
    · by_cases heq : l = w
      · rw [h9] at heq
        rw [heq] at hl1
        rw [hk] at hl1
        contradiction
      · have h11 := Nat.testBit_two_pow_of_ne (Ne.symm heq)
        rw [h11] at hl2
        contradiction
    · have h7 := Nat.testBit_two_pow w k
      have h8 : Nat.testBit (2 ^ w) k = false := by
        apply Bool.bool_eq_false
        replace h10: w ≠ k := Nat.ne_of_lt h10
        rw [h7]
        exact h10
      have h9 : ∀ j, k < j → Nat.testBit (2^w) j = Nat.testBit n j := by
        intros j h11
        rw [hj j h11]
        have h12 : w < j := Nat.lt_trans h10 h11
        have h13 := Nat.testBit_two_pow w j
        apply Bool.bool_eq_false
        replace h14: w ≠ j := Nat.ne_of_lt h12
        rw [h13]
        exact h14
      have H := Nat.lt_of_testBit k h8 hk h9
      exact Nat.lt_asymm hn H
    

   
    
    -- cases' Nat.eq_or_lt_of_le h8 with h9 h10
    -- · 
    -- · have h7 := Nat.testBit_two_pow w k
    --   have h8 : Nat.testBit (2 ^ w) k = false := by
    --     apply Bool.bool_eq_false
    --     replace h10: w ≠ k := Nat.ne_of_lt h10
    --     rw [h7]
    --     exact h10
    --   have h9 : ∀ j, k < j → Nat.testBit (2^w) j = Nat.testBit n j := by
    --     intros j h11
    --     rw [hj j h11]
    --     have h12 : w < j := Nat.lt_trans h10 h11
    --     have h13 := Nat.testBit_two_pow w j
    --     apply Bool.bool_eq_false
    --     replace h14: w ≠ j := Nat.ne_of_lt h12
    --     rw [h13]
    --     exact h14
    --   have H := Nat.lt_of_testBit k h8 hk h9
    --   exact Nat.lt_asymm hn H
      

        


        










    

    

    


