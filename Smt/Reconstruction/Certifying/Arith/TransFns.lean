/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

-- implementation of rules about transcendental functions from cvc5

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LibrarySearch
/- import Smt.Reconstruction.Certifying.Arith.TransFns.ArithTransPi -/

#check Real.pi

example : 3 < Real.pi := by library_search

