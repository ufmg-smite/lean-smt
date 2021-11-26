import Lean

import Smt.Solver
import Smt.Term

namespace Smt
namespace Constants

open Smt.Term
open Smt.Solver
open Lean

def natMinus : Expr := mkConst (Name.mkSimple "natMinus")

def defNatMinus : String :=
   genDefineFun "natMinus" [("x", `"Int"), ("y", `"Int")] (`"Int") $
    `"ite" • (`"<" • `"x" • `"y") • ``"0" • (`"-" • `"x" • `"y")

end Constants
end Smt
