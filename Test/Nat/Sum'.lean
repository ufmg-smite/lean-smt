-- import Smt

-- def sum (n : Nat) : Nat := if n = 0 then 0 else n + sum (n - 1)

-- theorem sum_formula : sum n = n * (n + 1) / 2 := by
--   induction n with
--   | zero => smt_show [sum]; rfl
--   | succ n ih =>
--     smt_show [sum, ih]
--     sorry
