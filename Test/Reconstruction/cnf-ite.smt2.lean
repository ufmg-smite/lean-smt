import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {U : Type u} [Nonempty U]
variable {d : U}
variable {b : U}
variable {b : U}
variable {c : U}
variable {a : U}
variable {f : (U -> U)}
variable {d : U}
variable {a : U}
variable {c : U}
variable {f : (U -> U)}
variable {e : U}
variable {e : U}

theorem th0 : (Eq (ite (Not (Eq (f a) d)) (Eq d e) (Eq d (f b))) (ite (Eq (f a) d) (Eq d (f b)) (Eq d e))) → (Eq (ite (Eq e (f a)) True (Eq e (f b))) (Or (Eq e (f a)) (Eq e (f b)))) → (Eq (Eq (f a) d) (Eq d (f a))) → (Eq (ite (Not (Eq (f a) e)) (Not (Eq e (f b))) (Eq a c)) (ite (Eq (f a) e) (Eq a c) (Not (Eq e (f b))))) → (Eq (ite (Not (Eq (f a) e)) (Eq e (f b)) (Eq a c)) (ite (Eq (f a) e) (Eq a c) (Eq e (f b)))) → (Eq (ite (Eq e (f a)) True (Not (Eq e (f b)))) (Or (Eq e (f a)) (Not (Eq e (f b))))) → (Eq (ite (Not (Eq (f a) d)) (Eq d e) (Not (Eq d (f b)))) (ite (Eq (f a) d) (Not (Eq d (f b))) (Eq d e))) → (Eq (Eq e e) True) → (Eq (Eq (f a) e) (Eq e (f a))) → (Eq (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c)) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e)) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq d e))) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq a c))) (Or (ite (Eq e (f a)) (Eq a c) (Eq e (f b))) (Or (Or (Eq e (f a)) (Eq e (f b))) (Or (Not (Or (Eq e (f a)) (Not (Eq e (f b))))) (Or (Not (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b))))) (Eq a b))))))))) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c)) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e)) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq d e))) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq a c))) (Or (ite (Eq e (f a)) (Eq a c) (Eq e (f b))) (Or (Not (Or (Eq e (f a)) (Not (Eq e (f b))))) (Or (Not (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b))))) (Or (Eq a b) (Or (Eq e (f a)) (Eq e (f b)))))))))))) → (Or (ite (Eq (f a) d) (Not (Eq d (f b))) (Eq a c)) (Or (ite (Not (Eq (f a) d)) (Eq d e) (Not (Eq d (f b)))) (Or (Not (ite (Not (Eq (f a) d)) (Eq d e) (Eq d (f b)))) (Or (Not (ite (Eq (f a) d) (Eq d (f b)) (Eq a c))) (Or (ite (Not (Eq (f a) e)) (Eq e (f b)) (Eq a c)) (Or (ite (Eq (f a) e) (Eq e e) (Eq e (f b))) (Or (Not (ite (Eq (f a) e) (Eq e e) (Not (Eq e (f b))))) (Or (Not (ite (Not (Eq (f a) e)) (Not (Eq e (f b))) (Eq a c))) (Eq a b))))))))) → (And (Eq (f a) d) (Eq d (f b))) → (And (Not (Eq (f a) e)) (Not (Eq e (f b)))) → (Not (Eq a b)) → False :=
fun lean_r0 : (Eq (ite (Not (Eq (f a) d)) (Eq d e) (Eq d (f b))) (ite (Eq (f a) d) (Eq d (f b)) (Eq d e))) =>
fun lean_r1 : (Eq (ite (Eq e (f a)) True (Eq e (f b))) (Or (Eq e (f a)) (Eq e (f b)))) =>
fun lean_r2 : (Eq (Eq (f a) d) (Eq d (f a))) =>
fun lean_r3 : (Eq (ite (Not (Eq (f a) e)) (Not (Eq e (f b))) (Eq a c)) (ite (Eq (f a) e) (Eq a c) (Not (Eq e (f b))))) =>
fun lean_r4 : (Eq (ite (Not (Eq (f a) e)) (Eq e (f b)) (Eq a c)) (ite (Eq (f a) e) (Eq a c) (Eq e (f b)))) =>
fun lean_r5 : (Eq (ite (Eq e (f a)) True (Not (Eq e (f b)))) (Or (Eq e (f a)) (Not (Eq e (f b))))) =>
fun lean_r6 : (Eq (ite (Not (Eq (f a) d)) (Eq d e) (Not (Eq d (f b)))) (ite (Eq (f a) d) (Not (Eq d (f b))) (Eq d e))) =>
fun lean_r7 : (Eq (Eq e e) True) =>
fun lean_r8 : (Eq (Eq (f a) e) (Eq e (f a))) =>
fun lean_r9 : (Eq (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c)) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e)) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq d e))) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq a c))) (Or (ite (Eq e (f a)) (Eq a c) (Eq e (f b))) (Or (Or (Eq e (f a)) (Eq e (f b))) (Or (Not (Or (Eq e (f a)) (Not (Eq e (f b))))) (Or (Not (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b))))) (Eq a b))))))))) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c)) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e)) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq d e))) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq a c))) (Or (ite (Eq e (f a)) (Eq a c) (Eq e (f b))) (Or (Not (Or (Eq e (f a)) (Not (Eq e (f b))))) (Or (Not (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b))))) (Or (Eq a b) (Or (Eq e (f a)) (Eq e (f b)))))))))))) =>
fun lean_a10 : (Or (ite (Eq (f a) d) (Not (Eq d (f b))) (Eq a c)) (Or (ite (Not (Eq (f a) d)) (Eq d e) (Not (Eq d (f b)))) (Or (Not (ite (Not (Eq (f a) d)) (Eq d e) (Eq d (f b)))) (Or (Not (ite (Eq (f a) d) (Eq d (f b)) (Eq a c))) (Or (ite (Not (Eq (f a) e)) (Eq e (f b)) (Eq a c)) (Or (ite (Eq (f a) e) (Eq e e) (Eq e (f b))) (Or (Not (ite (Eq (f a) e) (Eq e e) (Not (Eq e (f b))))) (Or (Not (ite (Not (Eq (f a) e)) (Not (Eq e (f b))) (Eq a c))) (Eq a b))))))))) =>
fun lean_a11 : (And (Eq (f a) d) (Eq d (f b))) =>
fun lean_a12 : (And (Not (Eq (f a) e)) (Not (Eq e (f b)))) =>
fun lean_a13 : (Not (Eq a b)) => by
have lean_s0 : (Eq Or Or) := rfl
have lean_s1 : (Eq (Not (Eq d (f b))) (Not (Eq d (f b)))) := rfl
have lean_s2 : (Eq (Eq a c) (Eq a c)) := rfl
have lean_s3 : (Eq (ite (Eq (f a) d) (Not (Eq d (f b))) (Eq a c)) (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c))) := congrIte lean_r2 lean_s1 lean_s2
let lean_s4 := congr lean_s0 lean_s3
have lean_s5 : (Eq (Eq d e) (Eq d e)) := rfl
have lean_s6 : (Eq (ite (Eq (f a) d) (Not (Eq d (f b))) (Eq d e)) (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e))) := congrIte lean_r2 lean_s1 lean_s5
have lean_s7 : (Eq (ite (Not (Eq (f a) d)) (Eq d e) (Not (Eq d (f b)))) (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e))) := Eq.trans lean_r6 lean_s6
let lean_s8 := congr lean_s0 lean_s7
have lean_s9 : (Eq (Eq d (f b)) (Eq d (f b))) := rfl
have lean_s10 : (Eq (ite (Eq (f a) d) (Eq d (f b)) (Eq d e)) (ite (Eq d (f a)) (Eq d (f b)) (Eq d e))) := congrIte lean_r2 lean_s9 lean_s5
have lean_s11 : (Eq (ite (Not (Eq (f a) d)) (Eq d e) (Eq d (f b))) (ite (Eq d (f a)) (Eq d (f b)) (Eq d e))) := Eq.trans lean_r0 lean_s10
have lean_s12 : (Eq (Not (ite (Not (Eq (f a) d)) (Eq d e) (Eq d (f b)))) (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq d e)))) := flipCongrArg lean_s11 [Not]
let lean_s13 := congr lean_s0 lean_s12
have lean_s14 : (Eq (ite (Eq (f a) d) (Eq d (f b)) (Eq a c)) (ite (Eq d (f a)) (Eq d (f b)) (Eq a c))) := congrIte lean_r2 lean_s9 lean_s2
have lean_s15 : (Eq (Not (ite (Eq (f a) d) (Eq d (f b)) (Eq a c))) (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq a c)))) := flipCongrArg lean_s14 [Not]
let lean_s16 := congr lean_s0 lean_s15
have lean_s17 : (Eq (Eq e (f b)) (Eq e (f b))) := rfl
have lean_s18 : (Eq (ite (Eq (f a) e) (Eq a c) (Eq e (f b))) (ite (Eq e (f a)) (Eq a c) (Eq e (f b)))) := congrIte lean_r8 lean_s2 lean_s17
have lean_s19 : (Eq (ite (Not (Eq (f a) e)) (Eq e (f b)) (Eq a c)) (ite (Eq e (f a)) (Eq a c) (Eq e (f b)))) := Eq.trans lean_r4 lean_s18
let lean_s20 := congr lean_s0 lean_s19
have lean_s21 : (Eq (ite (Eq (f a) e) (Eq e e) (Eq e (f b))) (ite (Eq e (f a)) True (Eq e (f b)))) := congrIte lean_r8 lean_r7 lean_s17
have lean_s22 : (Eq (ite (Eq (f a) e) (Eq e e) (Eq e (f b))) (Or (Eq e (f a)) (Eq e (f b)))) := Eq.trans lean_s21 lean_r1
let lean_s23 := congr lean_s0 lean_s22
have lean_s24 : (Eq (Not (Eq e (f b))) (Not (Eq e (f b)))) := rfl
have lean_s25 : (Eq (ite (Eq (f a) e) (Eq e e) (Not (Eq e (f b)))) (ite (Eq e (f a)) True (Not (Eq e (f b))))) := congrIte lean_r8 lean_r7 lean_s24
have lean_s26 : (Eq (ite (Eq (f a) e) (Eq e e) (Not (Eq e (f b)))) (Or (Eq e (f a)) (Not (Eq e (f b))))) := Eq.trans lean_s25 lean_r5
have lean_s27 : (Eq (Not (ite (Eq (f a) e) (Eq e e) (Not (Eq e (f b))))) (Not (Or (Eq e (f a)) (Not (Eq e (f b)))))) := flipCongrArg lean_s26 [Not]
let lean_s28 := congr lean_s0 lean_s27
have lean_s29 : (Eq (ite (Eq (f a) e) (Eq a c) (Not (Eq e (f b)))) (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b))))) := congrIte lean_r8 lean_s2 lean_s24
have lean_s30 : (Eq (ite (Not (Eq (f a) e)) (Not (Eq e (f b))) (Eq a c)) (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b))))) := Eq.trans lean_r3 lean_s29
have lean_s31 : (Eq (Not (ite (Not (Eq (f a) e)) (Not (Eq e (f b))) (Eq a c))) (Not (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b)))))) := flipCongrArg lean_s30 [Not]
let lean_s32 := congr lean_s0 lean_s31
have lean_s33 : (Eq (Eq a b) (Eq a b)) := rfl
let lean_s34 := congr lean_s32 lean_s33
let lean_s35 := congr lean_s28 lean_s34
let lean_s36 := congr lean_s23 lean_s35
let lean_s37 := congr lean_s20 lean_s36
let lean_s38 := congr lean_s16 lean_s37
let lean_s39 := congr lean_s13 lean_s38
let lean_s40 := congr lean_s8 lean_s39
have lean_s41 : (Eq (Or (ite (Eq (f a) d) (Not (Eq d (f b))) (Eq a c)) (Or (ite (Not (Eq (f a) d)) (Eq d e) (Not (Eq d (f b)))) (Or (Not (ite (Not (Eq (f a) d)) (Eq d e) (Eq d (f b)))) (Or (Not (ite (Eq (f a) d) (Eq d (f b)) (Eq a c))) (Or (ite (Not (Eq (f a) e)) (Eq e (f b)) (Eq a c)) (Or (ite (Eq (f a) e) (Eq e e) (Eq e (f b))) (Or (Not (ite (Eq (f a) e) (Eq e e) (Not (Eq e (f b))))) (Or (Not (ite (Not (Eq (f a) e)) (Not (Eq e (f b))) (Eq a c))) (Eq a b))))))))) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c)) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e)) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq d e))) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq a c))) (Or (ite (Eq e (f a)) (Eq a c) (Eq e (f b))) (Or (Or (Eq e (f a)) (Eq e (f b))) (Or (Not (Or (Eq e (f a)) (Not (Eq e (f b))))) (Or (Not (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b))))) (Eq a b)))))))))) := congr lean_s4 lean_s40
have lean_s42 : (Eq (Or (ite (Eq (f a) d) (Not (Eq d (f b))) (Eq a c)) (Or (ite (Not (Eq (f a) d)) (Eq d e) (Not (Eq d (f b)))) (Or (Not (ite (Not (Eq (f a) d)) (Eq d e) (Eq d (f b)))) (Or (Not (ite (Eq (f a) d) (Eq d (f b)) (Eq a c))) (Or (ite (Not (Eq (f a) e)) (Eq e (f b)) (Eq a c)) (Or (ite (Eq (f a) e) (Eq e e) (Eq e (f b))) (Or (Not (ite (Eq (f a) e) (Eq e e) (Not (Eq e (f b))))) (Or (Not (ite (Not (Eq (f a) e)) (Not (Eq e (f b))) (Eq a c))) (Eq a b))))))))) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c)) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e)) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq d e))) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq a c))) (Or (ite (Eq e (f a)) (Eq a c) (Eq e (f b))) (Or (Not (Or (Eq e (f a)) (Not (Eq e (f b))))) (Or (Not (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b))))) (Or (Eq a b) (Or (Eq e (f a)) (Eq e (f b)))))))))))) := Eq.trans lean_s41 lean_r9
have lean_s43 : (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c)) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e)) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq d e))) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq a c))) (Or (ite (Eq e (f a)) (Eq a c) (Eq e (f b))) (Or (Not (Or (Eq e (f a)) (Not (Eq e (f b))))) (Or (Not (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b))))) (Or (Eq a b) (Or (Eq e (f a)) (Eq e (f b))))))))))) := eqResolve lean_a10 lean_s42
have lean_s44 : (Or (Not (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c)) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e)) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq d e))) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq a c))) (Or (ite (Eq e (f a)) (Eq a c) (Eq e (f b))) (Or (Not (Or (Eq e (f a)) (Not (Eq e (f b))))) (Or (Not (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b))))) (Or (Eq a b) (Or (Eq e (f a)) (Eq e (f b)))))))))))) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c)) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e)) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq d e))) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq a c))) (Or (ite (Eq e (f a)) (Eq a c) (Eq e (f b))) (Or (Not (Or (Eq e (f a)) (Not (Eq e (f b))))) (Or (Not (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b))))) (Or (Eq a b) (Or (Eq e (f a)) (Eq e (f b)))))))))))) := @cnfOrPos [(ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c)), (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e)), (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq d e))), (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq a c))), (ite (Eq e (f a)) (Eq a c) (Eq e (f b))), (Not (Or (Eq e (f a)) (Not (Eq e (f b))))), (Not (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b))))), (Eq a b), (Eq e (f a)), (Eq e (f b))]
have lean_s45 : (Or (Not (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c))) (Or (Not (Eq d (f a))) (Not (Eq d (f b))))) := cnfItePos1
let lean_s46 := flipCongrArg lean_r2 [And]
have lean_s47 : (Eq (And (Eq (f a) d) (Eq d (f b))) (And (Eq d (f a)) (Eq d (f b)))) := congr lean_s46 lean_s9
have lean_s48 : (And (Eq d (f a)) (Eq d (f b))) := eqResolve lean_a11 lean_s47
have lean_s49 : (Eq d (f a)) := by andElim lean_s48, 0
let lean_s50 := by R2 lean_s45, lean_s49, (Eq d (f a)), [(- 1), 0]
have lean_s51 : (And (Eq d (f a)) (Eq d (f b))) := eqResolve lean_a11 lean_s47
have lean_s52 : (Eq d (f b)) := by andElim lean_s51, 1
have lean_s53 : (Not (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c))) := by R2 lean_s50, lean_s52, (Eq d (f b)), [(- 1), 0]
let lean_s54 := by R1 lean_s44, lean_s53, (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c)), [(- 1), 0]
have lean_s55 : (Or (Not (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e))) (Or (Not (Eq d (f a))) (Not (Eq d (f b))))) := cnfItePos1
have lean_s56 : (Eq d (f a)) := by andElim lean_s48, 0
let lean_s57 := by R2 lean_s55, lean_s56, (Eq d (f a)), [(- 1), 0]
have lean_s58 : (Eq d (f b)) := by andElim lean_s51, 1
have lean_s59 : (Not (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e))) := by R2 lean_s57, lean_s58, (Eq d (f b)), [(- 1), 0]
let lean_s60 := by R1 lean_s54, lean_s59, (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e)), [(- 1), 0]
have lean_s61 : (Or (ite (Eq d (f a)) (Eq d (f b)) (Eq d e)) (Or (Not (Eq d (f a))) (Not (Eq d (f b))))) := cnfIteNeg1
have lean_s62 : (Eq d (f a)) := by andElim lean_s48, 0
let lean_s63 := by R2 lean_s61, lean_s62, (Eq d (f a)), [(- 1), 0]
have lean_s64 : (Eq d (f b)) := by andElim lean_s51, 1
have lean_s65 : (ite (Eq d (f a)) (Eq d (f b)) (Eq d e)) := by R2 lean_s63, lean_s64, (Eq d (f b)), [(- 1), 0]
let lean_s66 := by R2 lean_s60, lean_s65, (ite (Eq d (f a)) (Eq d (f b)) (Eq d e)), [(- 1), 0]
have lean_s67 : (Or (ite (Eq d (f a)) (Eq d (f b)) (Eq a c)) (Or (Not (Eq d (f a))) (Not (Eq d (f b))))) := cnfIteNeg1
have lean_s68 : (Eq d (f a)) := by andElim lean_s48, 0
let lean_s69 := by R2 lean_s67, lean_s68, (Eq d (f a)), [(- 1), 0]
have lean_s70 : (Eq d (f b)) := by andElim lean_s51, 1
have lean_s71 : (ite (Eq d (f a)) (Eq d (f b)) (Eq a c)) := by R2 lean_s69, lean_s70, (Eq d (f b)), [(- 1), 0]
let lean_s72 := by R2 lean_s66, lean_s71, (ite (Eq d (f a)) (Eq d (f b)) (Eq a c)), [(- 1), 0]
have lean_s73 : (Or (Not (ite (Eq e (f a)) (Eq a c) (Eq e (f b)))) (Or (Eq e (f a)) (Eq e (f b)))) := cnfItePos2
have lean_s74 : (Eq (Not (Eq (f a) e)) (Not (Eq e (f a)))) := flipCongrArg lean_r8 [Not]
let lean_s75 := flipCongrArg lean_s74 [And]
have lean_s76 : (Eq (And (Not (Eq (f a) e)) (Not (Eq e (f b)))) (And (Not (Eq e (f a))) (Not (Eq e (f b))))) := congr lean_s75 lean_s24
have lean_s77 : (And (Not (Eq e (f a))) (Not (Eq e (f b)))) := eqResolve lean_a12 lean_s76
have lean_s78 : (Not (Eq e (f a))) := by andElim lean_s77, 0
let lean_s79 := by R1 lean_s73, lean_s78, (Eq e (f a)), [(- 1), 0]
have lean_s80 : (And (Not (Eq e (f a))) (Not (Eq e (f b)))) := eqResolve lean_a12 lean_s76
have lean_s81 : (Not (Eq e (f b))) := by andElim lean_s80, 1
have lean_s82 : (Not (ite (Eq e (f a)) (Eq a c) (Eq e (f b)))) := by R1 lean_s79, lean_s81, (Eq e (f b)), [(- 1), 0]
let lean_s83 := by R1 lean_s72, lean_s82, (ite (Eq e (f a)) (Eq a c) (Eq e (f b))), [(- 1), 0]
have lean_s84 : (Or (Or (Eq e (f a)) (Not (Eq e (f b)))) (Not (Not (Eq e (f b))))) := @cnfOrNeg [(Eq e (f a)), (Not (Eq e (f b)))] 1
have lean_s85 : (Not (Eq e (f b))) := by andElim lean_s80, 1
have lean_s86 : (Or (Eq e (f a)) (Not (Eq e (f b)))) := by R2 lean_s84, lean_s85, (Not (Eq e (f b))), [(- 1), 0]
let lean_s87 := by R2 lean_s83, lean_s86, (Or (Eq e (f a)) (Not (Eq e (f b)))), [(- 1), 0]
have lean_s88 : (Or (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b)))) (Or (Eq e (f a)) (Not (Not (Eq e (f b)))))) := cnfIteNeg2
have lean_s89 : (Not (Eq e (f a))) := by andElim lean_s77, 0
let lean_s90 := by R1 lean_s88, lean_s89, (Eq e (f a)), [(- 1), 0]
have lean_s91 : (Not (Eq e (f b))) := by andElim lean_s80, 1
have lean_s92 : (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b)))) := by R2 lean_s90, lean_s91, (Not (Eq e (f b))), [(- 1), 0]
let lean_s93 := by R2 lean_s87, lean_s92, (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b)))), [(- 1), 0]
let lean_s94 := by R1 lean_s93, lean_a13, (Eq a b), [(- 1), 0]
have lean_s95 : (Not (Eq e (f a))) := by andElim lean_s77, 0
let lean_s96 := by R1 lean_s94, lean_s95, (Eq e (f a)), [(- 1), 0]
have lean_s97 : (Not (Eq e (f b))) := by andElim lean_s80, 1
have lean_s98 : (Not (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq a c)) (Or (ite (Eq d (f a)) (Not (Eq d (f b))) (Eq d e)) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq d e))) (Or (Not (ite (Eq d (f a)) (Eq d (f b)) (Eq a c))) (Or (ite (Eq e (f a)) (Eq a c) (Eq e (f b))) (Or (Not (Or (Eq e (f a)) (Not (Eq e (f b))))) (Or (Not (ite (Eq e (f a)) (Eq a c) (Not (Eq e (f b))))) (Or (Eq a b) (Or (Eq e (f a)) (Eq e (f b)))))))))))) := by R1 lean_s96, lean_s97, (Eq e (f b)), [(- 1), 0]
exact (show False from contradiction lean_s43 lean_s98)

