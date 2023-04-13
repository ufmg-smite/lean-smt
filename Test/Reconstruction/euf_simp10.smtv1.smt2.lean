import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {A : Type u} [Nonempty A]
variable {f : (A -> A)}
variable {x : A}
variable {x : A}
variable {f : (A -> A)}

theorem th0 : (Eq (Eq (f (f (f (f (f x))))) (f x)) (Eq (f x) (f (f (f (f (f x))))))) → (Eq (Eq (f (f (f x))) (f x)) (Eq (f x) (f (f (f x))))) → (Not (Implies (And (Eq (f (f (f x))) (f x)) (Eq (f (f (f (f (f x))))) (f x))) (Eq (f (f (f x))) (f x)))) → False :=
fun lean_r0 : (Eq (Eq (f (f (f (f (f x))))) (f x)) (Eq (f x) (f (f (f (f (f x))))))) =>
fun lean_r1 : (Eq (Eq (f (f (f x))) (f x)) (Eq (f x) (f (f (f x))))) =>
fun lean_a2 : (Not (Implies (And (Eq (f (f (f x))) (f x)) (Eq (f (f (f (f (f x))))) (f x))) (Eq (f (f (f x))) (f x)))) => by
let lean_s0 := flipCongrArg lean_r1 [And]
have lean_s1 : (Eq (And (Eq (f (f (f x))) (f x)) (Eq (f (f (f (f (f x))))) (f x))) (And (Eq (f x) (f (f (f x)))) (Eq (f x) (f (f (f (f (f x)))))))) := congr lean_s0 lean_r0
let lean_s2 := flipCongrArg lean_s1 [Implies]
have lean_s3 : (Eq (Implies (And (Eq (f (f (f x))) (f x)) (Eq (f (f (f (f (f x))))) (f x))) (Eq (f (f (f x))) (f x))) (Implies (And (Eq (f x) (f (f (f x)))) (Eq (f x) (f (f (f (f (f x))))))) (Eq (f x) (f (f (f x)))))) := congr lean_s2 lean_r1
have lean_s4 : (Eq (Not (Implies (And (Eq (f (f (f x))) (f x)) (Eq (f (f (f (f (f x))))) (f x))) (Eq (f (f (f x))) (f x)))) (Not (Implies (And (Eq (f x) (f (f (f x)))) (Eq (f x) (f (f (f (f (f x))))))) (Eq (f x) (f (f (f x))))))) := flipCongrArg lean_s3 [Not]
have lean_s5 : (Not (Implies (And (Eq (f x) (f (f (f x)))) (Eq (f x) (f (f (f (f (f x))))))) (Eq (f x) (f (f (f x)))))) := eqResolve lean_a2 lean_s4
have lean_s6 : (And (Eq (f x) (f (f (f x)))) (Eq (f x) (f (f (f (f (f x))))))) := notImplies1 lean_s5
have lean_s7 : (Eq (f x) (f (f (f x)))) := by andElim lean_s6, 0
have lean_s8 : (Not (Implies (And (Eq (f x) (f (f (f x)))) (Eq (f x) (f (f (f (f (f x))))))) (Eq (f x) (f (f (f x)))))) := eqResolve lean_a2 lean_s4
have lean_s9 : (Not (Eq (f x) (f (f (f x))))) := notImplies2 lean_s8
exact (show False from contradiction lean_s7 lean_s9)
