/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Basic

theorem arithTransExpApproxAboveNeg (d l u t : Real) :
    let p: Real → Real := sorry
    let secant := ((p l - p u) / (l - u)) * (t - l) + p l
    t ≥ l ∧ t ≤ u → Real.exp t ≤ secant := sorry
