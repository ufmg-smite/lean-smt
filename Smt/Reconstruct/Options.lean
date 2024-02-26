/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

namespace Smt.Reconstruct

open Lean

initialize
  registerTraceClass `smt.profile.reconstruct
  registerTraceClass `smt.debug.reconstruct

end Smt.Reconstruct
