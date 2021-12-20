import Lean

import Smt.Solver
import Smt.Term

namespace Smt
namespace Constants

open Smt.Term
open Smt.Solver
open Lean

def natMinus : Expr := mkConst `Nat.sub

def defNat (s : Solver) : Solver := defineSort s "Nat" [] (Symbol "Int")

def defNatSub (s : Solver) : Solver :=
   defineFun s "Nat.sub" [("x", `"Nat"), ("y", `"Nat")] (`"Nat") $
    `"ite" • (`"<" • `"x" • `"y") • ``"0" • (`"-" • `"x" • `"y")

end Constants
end Smt
