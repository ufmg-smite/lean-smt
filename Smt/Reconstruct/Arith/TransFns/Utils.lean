/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

namespace Smt.Reconstruct.Arith

open Set Real

theorem concaveOn_sin_Icc : ConcaveOn ℝ (Icc 0 π) sin := StrictConcaveOn.concaveOn strictConcaveOn_sin_Icc

theorem strictConvexOn_sin_Icc : StrictConvexOn ℝ (Icc (- π) 0) sin := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc _ _) continuousOn_sin fun x hx => ?_
  rw [interior_Icc] at hx
  simp only [mem_Ioo] at hx
  simp
  have ⟨hx₁, hx₂⟩ := hx
  exact Real.sin_neg_of_neg_of_neg_pi_lt hx₂ hx₁

theorem convexOn_sin_Icc : ConvexOn ℝ (Icc (- π) 0) sin := StrictConvexOn.convexOn strictConvexOn_sin_Icc
