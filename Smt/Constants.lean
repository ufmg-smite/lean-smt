/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Solver
import Smt.Term

namespace Smt
namespace Constants

open Smt.Term
open Smt.Solver
open Lean

infixl:20  " • " => App
prefix:21 " ` " => Symbol
prefix:21 " `` " => Literal

def defNat (s : Solver) : Solver := defineSort s "Nat" [] (Symbol "Int")

def defNatSub (s : Solver) : Solver :=
   defineFun s "Nat.sub" [("x", `"Nat"), ("y", `"Nat")] (`"Nat") $
    `"ite" • (`"<" • `"x" • `"y") • ``"0" • (`"-" • `"x" • `"y")

/-- Map from known constants to corresponding SMT constant/function symbols. -/
def knownConsts : Std.HashMap Expr (Option Expr) :=
  List.foldr (fun (k, v) m => m.insert k v) Std.HashMap.empty
  [
    (mkConst `Eq [levelOne], mkConst (Name.mkSimple "=")),
    (mkConst `Ne [levelOne], mkConst `distinct),
    (mkConst `Prop, mkConst `Bool),
    (mkConst `True, mkConst `true),
    (mkConst `False, mkConst `false),
    (mkConst `Not, mkConst `not),
    (mkConst `And, mkConst `and),
    (mkConst `Or, mkConst `or),
    (mkConst `Iff, mkConst (Name.mkSimple "=")),
    (mkConst `ite  [levelOne], mkConst (Name.mkSimple "ite")),
    (mkConst `Exists [levelOne], mkConst `exists),
    (mkConst `BEq.beq [levelZero], mkConst (Name.mkSimple "=")),
    (mkConst `Bool.true, mkConst `true),
    (mkConst `Bool.false, mkConst `false),
    (mkConst `String.length, mkConst `str.len),
    (mkConst `String.replace, mkConst `str.replace_all),

    (mkConst `Neg.neg [levelZero], mkConst (Name.mkSimple "-")),
    (mkConst `HAdd.hAdd levelsZero, mkConst (Name.mkSimple "+")),
    (mkConst `HSub.hSub levelsZero, mkConst (Name.mkSimple "-")),
    (mkConst `HMul.hMul levelsZero, mkConst (Name.mkSimple "*")),
    (mkConst `HDiv.hDiv levelsZero, mkConst (Name.mkSimple "/")),
    (mkConst `HMod.hMod levelsZero, mkConst `mod),
    (mkConst `LT.lt [levelZero], mkConst (Name.mkSimple "<")),
    (mkConst `GT.gt [levelZero], mkConst (Name.mkSimple ">")),
    (mkConst `LE.le [levelZero], mkConst (Name.mkSimple "<=")),
    (mkConst `GE.ge [levelZero], mkConst (Name.mkSimple ">=")),

    (mkApp2 (mkConst `HSub.hSub levelsZero) (mkConst `Nat) (mkConst `Nat),
     mkConst `Nat.sub),
    (mkApp2 (mkConst `HDiv.hDiv levelsZero) (mkConst `Nat) (mkConst `Nat),
     mkConst `div),
    (mkApp2 (mkConst `HDiv.hDiv levelsZero) (mkConst `Int) (mkConst `Int),
     mkConst `div),

    (mkApp (mkConst `LT.lt [levelZero]) (mkConst `String),
     mkConst (Name.mkSimple "str.<")),
    ((mkApp2 (mkConst `HAppend.hAppend levelsZero)
             (mkConst `String) (mkConst `String),
     mkConst (Name.mkSimple "str.++")))
  ]
  where
    levelsZero := [levelZero, levelZero, levelZero]

end Constants
end Smt
