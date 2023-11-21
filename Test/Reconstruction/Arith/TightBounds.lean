import Smt

open Smt.Reconstruction.Certifying

example {a b : Int} : a < b → (a : Int) ≤ Int.ceil (Real.intCast.intCast b) - 1 := by
  intro h
  intTightUb h

example {a : Int} : Real.intCast.intCast a < (7.2 : Real) → a ≤ Int.ceil (7.2 : Real) - 1 := by
  intro h
  intTightUb h

example {a b : Int} : a > b → (a : Int) ≥ Int.floor (Real.intCast.intCast b) + 1 := by
  intro h
  intTightLb h

