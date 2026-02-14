import Smt

notation "ℕ" => Nat

theorem ABP_p2c_fail_inv_2_extracted_1_3 (st_p_bit st_c_bit : Bool) (st_p2c_bit : ℕ → Bool)
  (st_p2c_head st_p2c_tail : ℕ) (st_c2p_bit : ℕ → Bool) (st_c2p_head st_c2p_tail st_first_new : ℕ)
  (hinv_left : st_p_bit = st_c_bit → st_first_new ≤ st_c2p_tail)
  (hinv_right_left : (st_p_bit != st_c_bit) = true → st_first_new ≤ st_p2c_tail)
  (hinv_right_right_left :
    ∀ (N : ℕ), st_p_bit = st_c_bit → st_p2c_head ≤ N → N < st_p2c_tail → N ≥ 0 → st_p2c_bit N = st_p_bit)
  (hinv_right_right_right_left :
    ∀ (N : ℕ),
      st_p_bit = st_c_bit →
        st_c2p_head ≤ N → N < st_c2p_tail → N < st_first_new → N ≥ 0 → (st_c2p_bit N != st_p_bit) = true)
  (hinv_right_right_right_right_left :
    ∀ (N : ℕ),
      st_p_bit = st_c_bit → st_c2p_head ≤ N → N < st_c2p_tail → st_first_new ≤ N → N ≥ 0 → st_c2p_bit N = st_p_bit)
  (hinv_right_right_right_right_right_left :
    ∀ (N : ℕ),
      (st_p_bit != st_c_bit) = true → st_c2p_head ≤ N → N < st_c2p_tail → N ≥ 0 → (st_c2p_bit N != st_p_bit) = true)
  (hinv_right_right_right_right_right_right_left :
    ∀ (N : ℕ),
      (st_p_bit != st_c_bit) = true →
        st_p2c_head ≤ N → N < st_p2c_tail → N < st_first_new → N ≥ 0 → (st_p2c_bit N != st_p_bit) = true)
  (hinv_right_right_right_right_right_right_right :
    ∀ (N : ℕ),
      (st_p_bit != st_c_bit) = true →
        st_p2c_head ≤ N → N < st_p2c_tail → st_first_new ≤ N → N ≥ 0 → st_p2c_bit N = st_p_bit)
  (a : st_p2c_head < st_p2c_tail) (N : ℕ) (a_1 : st_p_bit = st_c_bit) (a_2 : st_p2c_head + 1 ≤ N)
  (a_3 : N < st_p2c_tail) (a_4 : N ≥ 0) : st_p2c_bit N = st_p_bit := by
  smt [
    hinv_left, hinv_right_left, hinv_right_right_left, hinv_right_right_right_left, hinv_right_right_right_right_left,
    hinv_right_right_right_right_right_left, hinv_right_right_right_right_right_right_left,
    hinv_right_right_right_right_right_right_right, a, a_1, a_2, a_3, a_4]
