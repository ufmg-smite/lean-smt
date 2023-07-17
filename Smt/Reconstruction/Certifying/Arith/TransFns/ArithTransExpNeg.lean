/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Mathlib.Data.Complex.Exponential

theorem arithTransExpNeg (t : ℝ) : t < 0 ↔ Real.exp t < 1 :=
  Iff.comm.mp Real.exp_lt_one_iff
