import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.Resolution
import Smt.Reconstruction.Certifying.Factor
import Smt.Reconstruction.Certifying.PermutateOr

set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {U : Type u}
variable {p1 : Prop}
variable {p2 : Prop}
variable {p3 : Prop}
variable {a : U}
variable {c : U}
variable {f : (U -> U -> U)}
variable {b : U}
variable {d : U}

theorem th0 : (Eq a b) → (Eq c d) → (And p1 True) → (Or (Not p1) (And p2 p3)) → (Or (Not p3) (Not (Eq (f a c) (f b d)))) → (Iff (Iff p3 True) p3) → (Iff (Iff p2 True) p2) → (Iff (And p1 True) p1) → (Iff (Iff p1 True) p1) → (Iff (Eq (f b d) (f b d)) True) → (Iff (Not True) False) → False :=
fun lean_a0 : (Eq a b) =>
fun lean_a1 : (Eq c d) =>
fun lean_a2 : (And p1 True) =>
fun lean_a3 : (Or (Not p1) (And p2 p3)) =>
fun lean_a4 : (Or (Not p3) (Not (Eq (f a c) (f b d)))) =>
fun lean_a5 : (Iff (Iff p3 True) p3) =>
fun lean_a6 : (Iff (Iff p2 True) p2) =>
fun lean_a7 : (Iff (And p1 True) p1) =>
fun lean_a8 : (Iff (Iff p1 True) p1) =>
fun lean_a9 : (Iff (Eq (f b d) (f b d)) True) =>
fun lean_a10 : (Iff (Not True) False) =>
have lean_s0 : p1 := eqResolve lean_a2 lean_a7
have lean_s1 : (And p2 p3) := by R2 lean_a3, lean_s0, p1

have lean_s2 : p3 := by andElim lean_s1, 1
have lean_s3 : (Not (Eq (f a c) (f b d))) := by R2 lean_a4, lean_s2, p3
have lean_s4 : (Eq Not Not) := rfl
have lean_s5 : (Eq Eq Eq) := rfl
have lean_s6 : (Eq f f) := rfl
have lean_s7 : p3 := by andElim lean_s1, 1
have lean_s8 : (Iff p3 (Iff p3 True)) := Iff.symm lean_a5
have lean_s9 : (Iff p3 True) := eqResolve lean_s7 lean_s8
have lean_s10 : (And p2 p3) := by R2 lean_a3, lean_s0, p1
have lean_s11 : p2 := by andElim lean_s10, 0
have lean_s12 : (Iff p2 (Iff p2 True)) := Iff.symm lean_a6
have lean_s13 : (Iff p2 True) := eqResolve lean_s11 lean_s12
have lean_s14 : p1 := eqResolve lean_a2 lean_a7
have lean_s15 : (Iff p1 (Iff p1 True)) := Iff.symm lean_a8
have lean_s16 : (Iff p1 True) := eqResolve lean_s14 lean_s15
let lean_s17 := And.intro lean_a1 lean_a0
let lean_s18 := And.intro lean_s16 lean_s17
let lean_s19 := And.intro lean_s13 lean_s18
have lean_s20 : (And (Iff p3 True) (And (Iff p2 True) (And (Iff p1 True) (And (Eq c d) (Eq a b))))) := And.intro lean_s9 lean_s19
have lean_s21 : (Eq a b) := by andElim lean_s20, 4
let lean_s22 := by smtCong lean_s6, lean_s21
have lean_s23 : (Eq c d) := by andElim lean_s20, 3
have lean_s24 : (Eq (f a c) (f b d)) := by smtCong lean_s22, lean_s23
let lean_s25 := by smtCong lean_s5, lean_s24
have lean_s26 : (Eq (f b d) (f b d)) := rfl
have lean_s27 : (Iff (Eq (f a c) (f b d)) (Eq (f b d) (f b d))) := by smtCong lean_s25, lean_s26
have lean_s28 : (Iff (Not (Eq (f a c) (f b d))) (Not (Eq (f b d) (f b d)))) := by smtCong lean_s4, lean_s27
have lean_s29 : (Eq Not Not) := rfl
have lean_s30 : (Iff (Not (Eq (f b d) (f b d))) (Not True)) := by smtCong lean_s29, lean_a9
have lean_s31 : (Iff (Not (Eq (f b d) (f b d))) False) := Iff.trans lean_s30 lean_a10
have lean_s32 : (Iff (Not (Eq (f a c) (f b d))) False) := Iff.trans lean_s28 lean_s31
show False from eqResolve lean_s3 lean_s32
