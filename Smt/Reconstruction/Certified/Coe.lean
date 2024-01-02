import Smt.Reconstruction.Certified.Types
import Smt.Reconstruction.Certified.Term

open Types
open Coe
open proof
open sort
open term

instance {Δ : SEnvironment} : CoeOut (interpSort Δ (atom 1)) Prop where
  coe e := e

instance {Δ : SEnvironment} : CoeOut (interpSort Δ boolSort) Prop where
  coe e := e

def coe' : (A = B) → A → B
| rfl, a => a
