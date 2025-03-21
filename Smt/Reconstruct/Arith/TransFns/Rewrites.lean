/-
Copyright (c) 2021-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Pi.Irrational
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/--
  This file adds support for rewrite rules that transform each
  transcendental function supported by cvc5 into either $sin$
  or $exp$. Reference:
    https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites-transcendentals
-/

theorem arithCosineElim : ∀ (x : Real) , Real.cos x = Real.sin (Real.pi / 2 - x) := by
  intro x
  rw [<- Real.cos_sub_pi_div_two]
  simp only [sub_sub_cancel_left, Real.cos_neg]

theorem arithTangentElim : ∀ (x : Real) , Real.tan x = Real.sin x / Real.cos x :=
  fun x => Real.tan_eq_sin_div_cos x

theorem arithCotangentElim : ∀ (x : Real) , Real.cot x = Real.cos x / Real.sin x :=
  fun x => Real.cot_eq_cos_div_sin x

theorem arithPiNotInteger : ∀ (m : Int) , ¬ (Real.pi = (m : Real)) :=
  Irrational.ne_int irrational_pi
