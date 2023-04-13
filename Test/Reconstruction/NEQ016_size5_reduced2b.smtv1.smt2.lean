import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {U : Type u} [Nonempty U]
variable {p4 : (U -> Prop)}
variable {c_0 : U}
variable {c7 : U}
variable {c7 : U}
variable {p4 : (U -> Prop)}
variable {c_0 : U}

theorem th0 : (Eq (Eq c_0 c7) (Eq c7 c_0)) → (Eq (And (Not (p4 c_0)) (And (p4 c_0) True)) (And (Not (p4 c_0)) (p4 c_0))) → (Eq (Eq c_0 c_0) True) → (And (Not (p4 c_0)) (And (p4 c7) (Eq c_0 c7))) → False :=
fun lean_r0 : (Eq (Eq c_0 c7) (Eq c7 c_0)) =>
fun lean_r1 : (Eq (And (Not (p4 c_0)) (And (p4 c_0) True)) (And (Not (p4 c_0)) (p4 c_0))) =>
fun lean_r2 : (Eq (Eq c_0 c_0) True) =>
fun lean_a3 : (And (Not (p4 c_0)) (And (p4 c7) (Eq c_0 c7))) => by
have lean_s0 : (Eq And And) := rfl
have lean_s1 : (Eq (Not (p4 c_0)) (Not (p4 c_0))) := rfl
let lean_s2 := congr lean_s0 lean_s1
have lean_s3 : (Eq (p4 c7) (p4 c7)) := rfl
let lean_s4 := congr lean_s0 lean_s3
let lean_s5 := congr lean_s4 lean_r0
have lean_s6 : (Eq (And (Not (p4 c_0)) (And (p4 c7) (Eq c_0 c7))) (And (Not (p4 c_0)) (And (p4 c7) (Eq c7 c_0)))) := congr lean_s2 lean_s5
have lean_s7 : (Eq And And) := rfl
have lean_s8 : (Eq (Not (p4 c_0)) (Not (p4 c_0))) := rfl
let lean_s9 := congr lean_s7 lean_s8
have lean_s10 : (And (Not (p4 c_0)) (And (p4 c7) (Eq c7 c_0))) := eqResolve lean_a3 lean_s6
have lean_s11 : (Eq c7 c_0) := by andElim lean_s10, 2
have lean_s12 : (Eq (p4 c7) (p4 c_0)) := flipCongrArg lean_s11 [p4]
let lean_s13 := congr lean_s7 lean_s12
let lean_s14 := flipCongrArg lean_s11 [Eq]
have lean_s15 : (Eq c_0 c_0) := rfl
have lean_s16 : (Eq (Eq c7 c_0) (Eq c_0 c_0)) := congr lean_s14 lean_s15
let lean_s17 := congr lean_s13 lean_s16
have lean_s18 : (Eq (And (Not (p4 c_0)) (And (p4 c7) (Eq c7 c_0))) (And (Not (p4 c_0)) (And (p4 c_0) (Eq c_0 c_0)))) := congr lean_s9 lean_s17
have lean_s19 : (Eq And And) := rfl
let lean_s20 := congr lean_s19 lean_s1
have lean_s21 : (Eq (p4 c_0) (p4 c_0)) := rfl
let lean_s22 := congr lean_s19 lean_s21
let lean_s23 := congr lean_s22 lean_r2
have lean_s24 : (Eq (And (Not (p4 c_0)) (And (p4 c_0) (Eq c_0 c_0))) (And (Not (p4 c_0)) (And (p4 c_0) True))) := congr lean_s20 lean_s23
have lean_s25 : (Eq (And (Not (p4 c_0)) (And (p4 c_0) (Eq c_0 c_0))) (And (Not (p4 c_0)) (p4 c_0))) := Eq.trans lean_s24 lean_r1
have lean_s26 : (Eq (And (Not (p4 c_0)) (And (p4 c7) (Eq c7 c_0))) (And (Not (p4 c_0)) (p4 c_0))) := Eq.trans lean_s18 lean_s25
have lean_s27 : (Eq (And (Not (p4 c_0)) (And (p4 c7) (Eq c_0 c7))) (And (Not (p4 c_0)) (p4 c_0))) := Eq.trans lean_s6 lean_s26
have lean_s28 : (And (Not (p4 c_0)) (p4 c_0)) := eqResolve lean_a3 lean_s27
have lean_s29 : (p4 c_0) := by andElim lean_s28, 1
have lean_s30 : (Not (p4 c_0)) := by andElim lean_s28, 0
exact (show False from by R1 lean_s29, lean_s30, (p4 c_0), [0, 0])
