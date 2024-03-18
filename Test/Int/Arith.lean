import Smt

example (n m : Int) (h : 0 < m) : n % m < m := by
  smt_show [h]
  sorry

example (n m k l : Int) : (n - m) * k + l = n*k - m*k + l := by
  smt_show
  sorry

example (n m k l : Int) (hN : n ≤ m) (hK : k ≤ l) : n + k ≤ m + l := by
  smt_show [hN, hK]
  sorry
