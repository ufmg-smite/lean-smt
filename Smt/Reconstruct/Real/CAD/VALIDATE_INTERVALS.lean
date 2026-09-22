import Lean
import CompPoly
import Smt.Reconstruct.Real.CAD.COVER

open Qq CompPoly Lean

def validateIntervalsCore (p_intervals : Array (Q(CPolynomial Rat) × Q(Cover.Piece Cover.Num)))
    (roots : Array RootVal) (root_map : Array (Q(CPolynomial Rat) × Array Nat)) : Smt.ReconstructM Expr :=
  pure (Expr.const `foo [])
