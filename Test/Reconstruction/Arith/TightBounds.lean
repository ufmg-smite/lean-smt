import Smt

open Smt.Reconstruct

example {a b : Int} : a < b → (a : Int) ≤ Int.ceil (Rat.ofInt b) - 1 := by
  intro h
  intTightUb h

example {a : Int} : Rat.ofInt a < (7 : ℚ) → a ≤ Int.ceil (7 : Int) - 1 := by
  intro h
  intTightUb h

example {a b : Int} : a > b → (a : Int) ≥ Int.floor (Rat.ofInt b) + 1 := by
  intro h
  intTightLb h
