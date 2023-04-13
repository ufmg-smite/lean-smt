import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {U : Type u} [Nonempty U]
variable {x : U}
variable {f : (U -> Prop)}
variable {y : U}
variable {x : U}
variable {y : U}
variable {f : (U -> Prop)}

theorem th0 : (And (f x) (And (Eq (f x) (f y)) (Not (f y)))) → False :=
fun lean_a0 : (And (f x) (And (Eq (f x) (f y)) (Not (f y)))) => by
have lean_s0 : (f x) := by andElim lean_a0, 0
have lean_s1 : (Eq (f x) (f y)) := by andElim lean_a0, 1
have lean_s2 : (f y) := eqResolve lean_s0 lean_s1
have lean_s3 : (Not (f y)) := by andElim lean_a0, 2
exact (show False from contradiction lean_s2 lean_s3)
