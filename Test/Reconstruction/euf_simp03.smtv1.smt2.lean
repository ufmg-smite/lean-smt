import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {U : Type u} [Nonempty U]
variable {z : U}
variable {x : U}
variable {x : U}
variable {f : (U -> U)}
variable {y : U}
variable {f : (U -> U)}
variable {z : U}
variable {y : U}

theorem th0 : (Eq (Eq (f x) y) (Eq y (f x))) → (Eq (Eq (f (f x)) (f x)) (Eq (f x) (f (f x)))) → (Eq (And (Not (Eq x (f (f x)))) (And (Eq (f (f x)) (f (f (f x)))) (And True (And True (And (Eq (f x) (f (f (f (f x))))) (Not (Eq (f x) (f (f x))))))))) (And (Not (Eq x (f (f x)))) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq (f x) (f (f (f (f x))))) (Not (Eq (f x) (f (f x)))))))) → (Eq (Eq (f (f x)) y) (Eq y (f (f x)))) → (Eq (Eq (f (f x)) (f (f x))) True) → (Eq (Eq (f x) z) (Eq z (f x))) → (Eq (Eq (f (f (f (f x)))) (f x)) (Eq (f x) (f (f (f (f x)))))) → (Eq (Eq (f (f (f (f x)))) z) (Eq z (f (f (f (f x)))))) → (Eq (Eq (f (f (f (f x)))) (f (f (f (f x))))) True) → (And (Not (Eq x y)) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq (f (f x)) y) (And (Eq (f (f (f (f x)))) z) (And (Eq (f x) z) (Not (Eq (f x) y))))))) → False :=
fun lean_r0 : (Eq (Eq (f x) y) (Eq y (f x))) =>
fun lean_r1 : (Eq (Eq (f (f x)) (f x)) (Eq (f x) (f (f x)))) =>
fun lean_r2 : (Eq (And (Not (Eq x (f (f x)))) (And (Eq (f (f x)) (f (f (f x)))) (And True (And True (And (Eq (f x) (f (f (f (f x))))) (Not (Eq (f x) (f (f x))))))))) (And (Not (Eq x (f (f x)))) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq (f x) (f (f (f (f x))))) (Not (Eq (f x) (f (f x)))))))) =>
fun lean_r3 : (Eq (Eq (f (f x)) y) (Eq y (f (f x)))) =>
fun lean_r4 : (Eq (Eq (f (f x)) (f (f x))) True) =>
fun lean_r5 : (Eq (Eq (f x) z) (Eq z (f x))) =>
fun lean_r6 : (Eq (Eq (f (f (f (f x)))) (f x)) (Eq (f x) (f (f (f (f x)))))) =>
fun lean_r7 : (Eq (Eq (f (f (f (f x)))) z) (Eq z (f (f (f (f x)))))) =>
fun lean_r8 : (Eq (Eq (f (f (f (f x)))) (f (f (f (f x))))) True) =>
fun lean_a9 : (And (Not (Eq x y)) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq (f (f x)) y) (And (Eq (f (f (f (f x)))) z) (And (Eq (f x) z) (Not (Eq (f x) y))))))) => by
have lean_s0 : (Or (And (Eq (f (f x)) (f (f (f x)))) (Eq (f x) (f (f (f (f x)))))) (Or (Not (Eq (f (f x)) (f (f (f x))))) (Not (Eq (f x) (f (f (f (f x)))))))) := cnfAndNeg [(Eq (f (f x)) (f (f (f x)))), (Eq (f x) (f (f (f (f x)))))]
have lean_s1 : (Or (Not (Eq (f (f x)) (f (f (f x))))) (Or (Not (Eq (f x) (f (f (f (f x)))))) (Eq (f x) (f (f x))))) :=
  (scope (fun lean_a10 : (Eq (f (f x)) (f (f (f x)))) =>
    (scope (fun lean_a11 : (Eq (f x) (f (f (f (f x))))) =>
      have lean_s1 : (Eq (f (f (f (f x)))) (f x)) := Eq.symm lean_a11
      have lean_s2 : (Eq (f x) (f (f (f (f x))))) := Eq.symm lean_s1
      have lean_s3 : (Eq (f (f (f x))) (f (f x))) := Eq.symm lean_a10
      have lean_s4 : (Eq (f (f (f (f x)))) (f (f (f x)))) := flipCongrArg lean_s3 [f]
      let lean_s5 := Eq.trans lean_s2 lean_s4
      have lean_s6 : (Eq (f x) (f (f x))) := Eq.trans lean_s5 lean_s3
      show (Eq (f x) (f (f x))) from lean_s6
  ))))
have lean_s2 : (Implies (And (Eq (f (f x)) (f (f (f x)))) (Eq (f x) (f (f (f (f x)))))) (Eq (f x) (f (f x)))) := by liftOrNToImp lean_s1, 2
have lean_s3 : (Or (Not (And (Eq (f (f x)) (f (f (f x)))) (Eq (f x) (f (f (f (f x))))))) (Eq (f x) (f (f x)))) := impliesElim lean_s2
have lean_s4 : (Or (Not (Eq (f (f x)) (f (f (f x))))) (Or (Not (Eq (f x) (f (f (f (f x)))))) (Eq (f x) (f (f x))))) := by R1 lean_s0, lean_s3, (And (Eq (f (f x)) (f (f (f x)))) (Eq (f x) (f (f (f (f x)))))), [(- 1), (- 1)]
have lean_s5 : (Or (Eq (f x) (f (f x))) (Or (Not (Eq (f (f x)) (f (f (f x))))) (Not (Eq (f x) (f (f (f (f x)))))))) := by permutateOr lean_s4, [2, 0, 1], (- 1)
have lean_s6 : (Eq And And) := rfl
have lean_s7 : (Eq (Not (Eq x y)) (Not (Eq x y))) := rfl
let lean_s8 := congr lean_s6 lean_s7
have lean_s9 : (Eq (Eq (f (f x)) (f (f (f x)))) (Eq (f (f x)) (f (f (f x))))) := rfl
let lean_s10 := congr lean_s6 lean_s9
let lean_s11 := congr lean_s6 lean_r3
let lean_s12 := congr lean_s6 lean_r7
let lean_s13 := congr lean_s6 lean_r5
have lean_s14 : (Eq (Not (Eq (f x) y)) (Not (Eq y (f x)))) := flipCongrArg lean_r0 [Not]
let lean_s15 := congr lean_s13 lean_s14
let lean_s16 := congr lean_s12 lean_s15
let lean_s17 := congr lean_s11 lean_s16
let lean_s18 := congr lean_s10 lean_s17
have lean_s19 : (Eq (And (Not (Eq x y)) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq (f (f x)) y) (And (Eq (f (f (f (f x)))) z) (And (Eq (f x) z) (Not (Eq (f x) y))))))) (And (Not (Eq x y)) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq y (f (f x))) (And (Eq z (f (f (f (f x))))) (And (Eq z (f x)) (Not (Eq y (f x))))))))) := congr lean_s8 lean_s18
have lean_s20 : (Eq And And) := rfl
have lean_s21 : (Eq x x) := rfl
let lean_s22 := flipCongrArg lean_s21 [Eq]
have lean_s23 : (And (Not (Eq x y)) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq y (f (f x))) (And (Eq z (f (f (f (f x))))) (And (Eq z (f x)) (Not (Eq y (f x)))))))) := eqResolve lean_a9 lean_s19
have lean_s24 : (Eq z (f (f (f (f x))))) := by andElim lean_s23, 3
have lean_s25 : (And (Not (Eq x y)) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq y (f (f x))) (And (Eq z (f (f (f (f x))))) (And (Eq z (f x)) (Not (Eq y (f x)))))))) := eqResolve lean_a9 lean_s19
have lean_s26 : (Eq y (f (f x))) := by andElim lean_s25, 2
have lean_s27 : (And (Eq z (f (f (f (f x))))) (Eq y (f (f x)))) := And.intro lean_s24 lean_s26
have lean_s28 : (Eq y (f (f x))) := by andElim lean_s27, 1
have lean_s29 : (Eq (Eq x y) (Eq x (f (f x)))) := congr lean_s22 lean_s28
have lean_s30 : (Eq (Not (Eq x y)) (Not (Eq x (f (f x))))) := flipCongrArg lean_s29 [Not]
let lean_s31 := congr lean_s20 lean_s30
have lean_s32 : (Eq (Eq (f (f x)) (f (f (f x)))) (Eq (f (f x)) (f (f (f x))))) := rfl
let lean_s33 := congr lean_s20 lean_s32
let lean_s34 := flipCongrArg lean_s28 [Eq]
have lean_s35 : (Eq (f (f x)) (f (f x))) := rfl
have lean_s36 : (Eq (Eq y (f (f x))) (Eq (f (f x)) (f (f x)))) := congr lean_s34 lean_s35
let lean_s37 := congr lean_s20 lean_s36
have lean_s38 : (Eq z (f (f (f (f x))))) := by andElim lean_s27, 0
let lean_s39 := flipCongrArg lean_s38 [Eq]
have lean_s40 : (Eq (f (f (f (f x)))) (f (f (f (f x))))) := rfl
have lean_s41 : (Eq (Eq z (f (f (f (f x))))) (Eq (f (f (f (f x)))) (f (f (f (f x)))))) := congr lean_s39 lean_s40
let lean_s42 := congr lean_s20 lean_s41
let lean_s43 := flipCongrArg lean_s38 [Eq]
have lean_s44 : (Eq (f x) (f x)) := rfl
have lean_s45 : (Eq (Eq z (f x)) (Eq (f (f (f (f x)))) (f x))) := congr lean_s43 lean_s44
let lean_s46 := congr lean_s20 lean_s45
let lean_s47 := flipCongrArg lean_s28 [Eq]
have lean_s48 : (Eq (Eq y (f x)) (Eq (f (f x)) (f x))) := congr lean_s47 lean_s44
have lean_s49 : (Eq (Not (Eq y (f x))) (Not (Eq (f (f x)) (f x)))) := flipCongrArg lean_s48 [Not]
let lean_s50 := congr lean_s46 lean_s49
let lean_s51 := congr lean_s42 lean_s50
let lean_s52 := congr lean_s37 lean_s51
let lean_s53 := congr lean_s33 lean_s52
have lean_s54 : (Eq (And (Not (Eq x y)) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq y (f (f x))) (And (Eq z (f (f (f (f x))))) (And (Eq z (f x)) (Not (Eq y (f x)))))))) (And (Not (Eq x (f (f x)))) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq (f (f x)) (f (f x))) (And (Eq (f (f (f (f x)))) (f (f (f (f x))))) (And (Eq (f (f (f (f x)))) (f x)) (Not (Eq (f (f x)) (f x))))))))) := congr lean_s31 lean_s53
have lean_s55 : (Eq And And) := rfl
have lean_s56 : (Eq (Not (Eq x (f (f x)))) (Not (Eq x (f (f x))))) := rfl
let lean_s57 := congr lean_s55 lean_s56
let lean_s58 := congr lean_s55 lean_s9
let lean_s59 := congr lean_s55 lean_r4
let lean_s60 := congr lean_s55 lean_r8
let lean_s61 := congr lean_s55 lean_r6
have lean_s62 : (Eq (Not (Eq (f (f x)) (f x))) (Not (Eq (f x) (f (f x))))) := flipCongrArg lean_r1 [Not]
let lean_s63 := congr lean_s61 lean_s62
let lean_s64 := congr lean_s60 lean_s63
let lean_s65 := congr lean_s59 lean_s64
let lean_s66 := congr lean_s58 lean_s65
have lean_s67 : (Eq (And (Not (Eq x (f (f x)))) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq (f (f x)) (f (f x))) (And (Eq (f (f (f (f x)))) (f (f (f (f x))))) (And (Eq (f (f (f (f x)))) (f x)) (Not (Eq (f (f x)) (f x)))))))) (And (Not (Eq x (f (f x)))) (And (Eq (f (f x)) (f (f (f x)))) (And True (And True (And (Eq (f x) (f (f (f (f x))))) (Not (Eq (f x) (f (f x)))))))))) := congr lean_s57 lean_s66
have lean_s68 : (Eq (And (Not (Eq x (f (f x)))) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq (f (f x)) (f (f x))) (And (Eq (f (f (f (f x)))) (f (f (f (f x))))) (And (Eq (f (f (f (f x)))) (f x)) (Not (Eq (f (f x)) (f x)))))))) (And (Not (Eq x (f (f x)))) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq (f x) (f (f (f (f x))))) (Not (Eq (f x) (f (f x)))))))) := Eq.trans lean_s67 lean_r2
have lean_s69 : (Eq (And (Not (Eq x y)) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq y (f (f x))) (And (Eq z (f (f (f (f x))))) (And (Eq z (f x)) (Not (Eq y (f x)))))))) (And (Not (Eq x (f (f x)))) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq (f x) (f (f (f (f x))))) (Not (Eq (f x) (f (f x)))))))) := Eq.trans lean_s54 lean_s68
have lean_s70 : (Eq (And (Not (Eq x y)) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq (f (f x)) y) (And (Eq (f (f (f (f x)))) z) (And (Eq (f x) z) (Not (Eq (f x) y))))))) (And (Not (Eq x (f (f x)))) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq (f x) (f (f (f (f x))))) (Not (Eq (f x) (f (f x)))))))) := Eq.trans lean_s19 lean_s69
have lean_s71 : (And (Not (Eq x (f (f x)))) (And (Eq (f (f x)) (f (f (f x)))) (And (Eq (f x) (f (f (f (f x))))) (Not (Eq (f x) (f (f x))))))) := eqResolve lean_a9 lean_s70
have lean_s72 : (Not (Eq (f x) (f (f x)))) := by andElim lean_s71, 3
let lean_s73 := by R1 lean_s5, lean_s72, (Eq (f x) (f (f x))), [(- 1), 0]
have lean_s74 : (Eq (f x) (f (f (f (f x))))) := by andElim lean_s71, 2
let lean_s75 := by R2 lean_s73, lean_s74, (Eq (f x) (f (f (f (f x))))), [(- 1), 0]
have lean_s76 : (Eq (f (f x)) (f (f (f x)))) := by andElim lean_s71, 1
exact (show False from by R2 lean_s75, lean_s76, (Eq (f (f x)) (f (f (f x)))), [0, 0])
