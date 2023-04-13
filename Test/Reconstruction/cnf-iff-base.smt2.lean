import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {U : Type u} [Nonempty U]
variable {a : U}
variable {d : U}
variable {b : U}
variable {d : U}
variable {f : (U -> U)}
variable {b : U}
variable {f : (U -> U)}
variable {a : U}

theorem th0 : (Eq (Not (Not (Eq d (f a)))) (Eq d (f a))) → (Eq (Eq (Eq d (f a)) (Eq d (f a))) True) → (Eq (Eq (Not (Not (Eq d (f a)))) (Eq d (f a))) (Eq (Eq d (f a)) (Not (Not (Eq d (f a)))))) → (Eq (Not (Not (Eq d (f b)))) (Eq d (f b))) → (Eq (Eq (Not (Not (Eq d (f b)))) (Eq d (f b))) (Eq (Eq d (f b)) (Not (Not (Eq d (f b)))))) → (Eq (Eq (Eq d (f b)) (Eq d (f b))) True) → (Eq (Eq (Not (Eq d (f a))) (Not (Eq d (f b)))) (Eq (Not (Eq d (f b))) (Not (Eq d (f a))))) → (Eq (Eq (f a) d) (Eq d (f a))) → (Eq (Not (Eq (f a) d)) (Not (Eq d (f b)))) → (Or (Not (Eq (f a) d)) (Not (Eq d (f b)))) → (Or (Eq (f a) d) (Eq d (f b))) → False :=
fun lean_r0 : (Eq (Not (Not (Eq d (f a)))) (Eq d (f a))) =>
fun lean_r1 : (Eq (Eq (Eq d (f a)) (Eq d (f a))) True) =>
fun lean_r2 : (Eq (Eq (Not (Not (Eq d (f a)))) (Eq d (f a))) (Eq (Eq d (f a)) (Not (Not (Eq d (f a)))))) =>
fun lean_r3 : (Eq (Not (Not (Eq d (f b)))) (Eq d (f b))) =>
fun lean_r4 : (Eq (Eq (Not (Not (Eq d (f b)))) (Eq d (f b))) (Eq (Eq d (f b)) (Not (Not (Eq d (f b)))))) =>
fun lean_r5 : (Eq (Eq (Eq d (f b)) (Eq d (f b))) True) =>
fun lean_r6 : (Eq (Eq (Not (Eq d (f a))) (Not (Eq d (f b)))) (Eq (Not (Eq d (f b))) (Not (Eq d (f a))))) =>
fun lean_r7 : (Eq (Eq (f a) d) (Eq d (f a))) =>
fun lean_a8 : (Eq (Not (Eq (f a) d)) (Not (Eq d (f b)))) =>
fun lean_a9 : (Or (Not (Eq (f a) d)) (Not (Eq d (f b)))) =>
fun lean_a10 : (Or (Eq (f a) d) (Eq d (f b))) => by
have lean_s0 : (Eq (Not (Eq (f a) d)) (Not (Eq d (f a)))) := flipCongrArg lean_r7 [Not]
let lean_s1 := flipCongrArg lean_s0 [Or]
have lean_s2 : (Eq (Not (Eq d (f b))) (Not (Eq d (f b)))) := rfl
have lean_s3 : (Eq (Or (Not (Eq (f a) d)) (Not (Eq d (f b)))) (Or (Not (Eq d (f a))) (Not (Eq d (f b))))) := congr lean_s1 lean_s2
have lean_s4 : (Or (Not (Eq d (f a))) (Not (Eq d (f b)))) := eqResolve lean_a9 lean_s3
have lean_s5 : (Or (Not (Eq d (f b))) (Not (Eq d (f a)))) := by permutateOr lean_s4, [1, 0], (- 1)
let lean_s6 := flipCongrArg lean_s0 [Eq]
have lean_s7 : (Eq (Eq (Not (Eq (f a) d)) (Not (Eq d (f b)))) (Eq (Not (Eq d (f a))) (Not (Eq d (f b))))) := congr lean_s6 lean_s2
have lean_s8 : (Eq (Eq (Not (Eq (f a) d)) (Not (Eq d (f b)))) (Eq (Not (Eq d (f b))) (Not (Eq d (f a))))) := Eq.trans lean_s7 lean_r6
have lean_s9 : (Eq (Not (Eq d (f b))) (Not (Eq d (f a)))) := eqResolve lean_a8 lean_s8
have lean_s10 : (Or (Not (Eq d (f b))) (Not (Not (Eq d (f a))))) := equivElim2 lean_s9
have lean_s11 : (Eq (Not (Eq d (f b))) (Not (Eq d (f b)))) := rfl
let lean_s12 := flipCongrArg lean_s11 [Or]
have lean_s13 : (Eq (Eq d (f a)) (Eq d (f a))) := rfl
let lean_s14 := flipCongrArg lean_s13 [Eq]
have lean_s15 : (Eq (Eq (Eq d (f a)) (Not (Not (Eq d (f a))))) (Eq (Eq d (f a)) (Eq d (f a)))) := congr lean_s14 lean_r0
have lean_s16 : (Eq (Eq (Eq d (f a)) (Not (Not (Eq d (f a))))) True) := Eq.trans lean_s15 lean_r1
have lean_s17 : (Eq (Eq (Not (Not (Eq d (f a)))) (Eq d (f a))) True) := Eq.trans lean_r2 lean_s16
have lean_s18 : (Eq (Not (Not (Eq d (f a)))) (Eq d (f a))) := trueElim lean_s17
have lean_s19 : (Eq (Or (Not (Eq d (f b))) (Not (Not (Eq d (f a))))) (Or (Not (Eq d (f b))) (Eq d (f a)))) := congr lean_s12 lean_s18
have lean_s20 : (Or (Not (Eq d (f b))) (Eq d (f a))) := eqResolve lean_s10 lean_s19
let lean_s21 := flipCongrArg lean_r7 [Or]
have lean_s22 : (Eq (Eq d (f b)) (Eq d (f b))) := rfl
have lean_s23 : (Eq (Or (Eq (f a) d) (Eq d (f b))) (Or (Eq d (f a)) (Eq d (f b)))) := congr lean_s21 lean_s22
have lean_s24 : (Or (Eq d (f a)) (Eq d (f b))) := eqResolve lean_a10 lean_s23
have lean_s25 : (Or (Eq d (f b)) (Eq d (f a))) := by permutateOr lean_s24, [1, 0], (- 1)
have lean_s26 : (Or (Not (Not (Eq d (f b)))) (Not (Eq d (f a)))) := equivElim1 lean_s9
let lean_s27 := flipCongrArg lean_s22 [Eq]
have lean_s28 : (Eq (Eq (Eq d (f b)) (Not (Not (Eq d (f b))))) (Eq (Eq d (f b)) (Eq d (f b)))) := congr lean_s27 lean_r3
have lean_s29 : (Eq (Eq (Eq d (f b)) (Not (Not (Eq d (f b))))) True) := Eq.trans lean_s28 lean_r5
have lean_s30 : (Eq (Eq (Not (Not (Eq d (f b)))) (Eq d (f b))) True) := Eq.trans lean_r4 lean_s29
have lean_s31 : (Eq (Not (Not (Eq d (f b)))) (Eq d (f b))) := trueElim lean_s30
let lean_s32 := flipCongrArg lean_s31 [Or]
have lean_s33 : (Eq (Not (Eq d (f a))) (Not (Eq d (f a)))) := rfl
have lean_s34 : (Eq (Or (Not (Not (Eq d (f b)))) (Not (Eq d (f a)))) (Or (Eq d (f b)) (Not (Eq d (f a))))) := congr lean_s32 lean_s33
have lean_s35 : (Or (Eq d (f b)) (Not (Eq d (f a)))) := eqResolve lean_s26 lean_s34
have lean_s36 : (Or (Eq d (f b)) (Eq d (f b))) := by R1 lean_s25, lean_s35, (Eq d (f a)), [(- 1), (- 1)]
have lean_s37 : (Eq d (f b)) := by factor lean_s36, 1
have lean_s38 : (Eq d (f a)) := by R2 lean_s20, lean_s37, (Eq d (f b)), [(- 1), 0]
let lean_s39 := by R2 lean_s5, lean_s38, (Eq d (f a)), [(- 1), 0]
exact (show False from by R2 lean_s39, lean_s37, (Eq d (f b)), [0, 0])
