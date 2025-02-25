/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/


import Smt.Reconstruct.Arith.TransFns.ArithTransSineApproxBelowNeg

open Set Real

namespace Smt.Reconstruct.Arith

theorem arithTransSineApproxAbovePos (d k : ℕ) (hd : d = 4*k + 1)
                                     (hx : 0 < x) (hx2 : x ≤ π) :
    Real.sin x ≤ taylorWithinEval Real.sin d Set.univ 0 x := by
  rw [← neg_neg x, sin_neg, taylorSin_neg, neg_le_neg_iff]
  apply arithTransSineApproxBelowNeg d k hd (by linarith) (by linarith)
