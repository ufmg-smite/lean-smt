import Smt.Reconstruct.Arith

open Smt.Reconstruct.Arith

example (a : Int) : (a + 3) > 0 → (a + 3) ^ 2 > 0 := by
  arithMulSign [(a + 3)], [1], [2]

example (a : Int) : a < 0 → a ^ 3 < 0 := by
  arithMulSign [a], [-1], [3]

example (a b : ℚ) : a > 0 → b < 0 → a ^ 2 * b ^ 3 < 0 := by
  arithMulSign [a,b], [1,-1], [2,3]

example (a b c d e : Int) :
  a < 0 →
    b > 0 →
      c < 0 →
        d > 0 →
          e < 0 →
            a * (b ^ 2) * (c ^ 2) * (d ^ 4) * (e ^ 5) > 0 := by
  arithMulSign [a,b,c,d,e], [-1,1,-1,1,-1], [1,2,2,4,5]

example (a : Int) (b : ℚ) : a < 0 → b < 0 → a ^ 3 * b ^ 3 > 0 := by
  arithMulSign [a,b], [-1,-1], [3,3]

example (a e : Int) (b c d : ℚ) :
  a < 0 →
    b > 0 →
      c < 0 →
        d > 0 →
          e < 0 →
            a * (b ^ 2) * (c ^ 2) * (d ^ 4) * (e ^ 5) > 0 := by
  arithMulSign [a,b,c,d,e], [-1,1,-1,1,-1], [1,2,2,4,5]
