/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Tomaz Gomes Mascarenhas
-/

import Smt.Solver
import Smt.Term

namespace Smt.Constants

open Smt.Solver
open Smt.Term

infixl:20 " • "  => App
prefix:21 " ` "  => Symbol
prefix:21 " `` " => Literal

def defNat (s : Solver) : Solver := defineSort s "Nat" [] (Symbol "Int")

def defNatSub (s : Solver) : Solver :=
   defineFun s "Nat.sub" [("x", `"Nat"), ("y", `"Nat")] (`"Nat") $
    `"ite" • (`"<" • `"x" • `"y") • ``"0" • (`"-" • `"x" • `"y")

end Smt.Constants
