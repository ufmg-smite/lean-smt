/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Smt.Transformer

namespace Smt.Int

open Lean Expr
open Smt.Transformer

@[Smt] def replaceConst : Transformer
  | const `Int.ofNat .. => pure none
  | const `Int.neg ..   => pure (mkConst (Name.mkSimple "-"))
  | const `Int.le ..    => pure (mkConst (Name.mkSimple "<="))
  | e                   => pure e

end Smt.Int
