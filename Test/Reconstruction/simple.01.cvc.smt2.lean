import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {B : Type u} [Nonempty B]
variable {A : Type u} [Nonempty A]
variable {f : (A -> B)}
variable {y : A}
variable {x : A}
variable {y : A}
variable {x : A}
variable {f : (A -> B)}

theorem th0 : (Eq (Eq (f y) (f y)) True) → (Eq (Not True) False) → (Not (Implies (Eq x y) (Eq (f x) (f y)))) → False :=
fun lean_r0 : (Eq (Eq (f y) (f y)) True) =>
fun lean_r1 : (Eq (Not True) False) =>
fun lean_a2 : (Not (Implies (Eq x y) (Eq (f x) (f y)))) => by
have lean_s0 : (Not (Eq (f x) (f y))) := notImplies2 lean_a2
have lean_s1 : (Eq x y) := notImplies1 lean_a2
have lean_s2 : (Eq (f x) (f y)) := flipCongrArg lean_s1 [f]
let lean_s3 := flipCongrArg lean_s2 [Eq]
have lean_s4 : (Eq (f y) (f y)) := rfl
have lean_s5 : (Eq (Eq (f x) (f y)) (Eq (f y) (f y))) := congr lean_s3 lean_s4
have lean_s6 : (Eq (Not (Eq (f x) (f y))) (Not (Eq (f y) (f y)))) := flipCongrArg lean_s5 [Not]
have lean_s7 : (Eq (Not (Eq (f y) (f y))) (Not True)) := flipCongrArg lean_r0 [Not]
have lean_s8 : (Eq (Not (Eq (f y) (f y))) False) := Eq.trans lean_s7 lean_r1
have lean_s9 : (Eq (Not (Eq (f x) (f y))) False) := Eq.trans lean_s6 lean_s8
exact (show False from eqResolve lean_s0 lean_s9)
