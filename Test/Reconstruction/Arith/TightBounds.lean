import Smt.Reconstruct.Arith

open Smt.Reconstruct.Arith

example {a b : Int} : a < b → (a : Int) ≤ Int.ceil (Real.instIntCast.intCast b) - 1 := by
  intro h
  intTightUb h

example {a : Int} : Real.instIntCast.intCast a < (7.2 : Real) → a ≤ Int.ceil (7.2 : Real) - 1 := by
  intro h
  intTightUb h

example {a b : Int} : a > b → (a : Int) ≥ Int.floor (Real.instIntCast.intCast b) + 1 := by
  intro h
  intTightLb h
