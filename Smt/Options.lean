/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Tomaz Gomes Mascarenhas
-/

module

public import Lean
public meta import Lean

public meta section

namespace Smt

open Lean

initialize
  registerTraceClass `smt
  registerTraceClass `smt.attr
  registerTraceClass `smt.preprocess
  registerTraceClass `smt.translate
  registerTraceClass `smt.translate.expr
  registerTraceClass `smt.translate.query
  registerTraceClass `smt.solve
  registerTraceClass `smt.reconstruct
  registerTraceClass `smt.reconstruct.sort
  registerTraceClass `smt.reconstruct.term
  registerTraceClass `smt.reconstruct.proof

end Smt
