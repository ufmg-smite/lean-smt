/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic.LibrarySearch

import Smt.Reconstruction.Certifying.Boolean

open Smt.Reconstruction.Certifying

theorem arithTransExpSuperLin' (t : ℝ) :
    t > 0 → Real.exp t > t + 1 :=
  Real.add_one_lt_exp_of_pos

theorem arithTransExpSuperLin (t : ℝ) :
    t ≤ 0 ∨ Real.exp t > t + 1 := by
  apply orImplies
  intro h
  simp at h
  exact arithTransExpSuperLin' t h
