import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {U : Type u} [Nonempty U]
variable {f : (U -> U)}
variable {g : (U -> U)}
variable {z : U}
variable {y : U}
variable {z : U}
variable {x : U}
variable {x : U}
variable {g : (U -> U)}
variable {y : U}
variable {f : (U -> U)}

theorem th0 : (Eq (Not (Not (Eq x y))) (Eq x y)) → (Eq (Eq (Not (Not (Eq x y))) (Eq x y)) (Eq (Eq x y) (Not (Not (Eq x y))))) → (Eq (Eq (f z) z) (Eq z (f z))) → (Eq (Eq (g z) z) (Eq z (g z))) → (Eq (Eq (f x) x) (Eq x (f x))) → (Eq (Eq (Eq x y) (Eq x y)) True) → (Eq (Eq (g y) y) (Eq y (g y))) → (And (Not (Eq x y)) (And (Eq (f x) (f z)) (And (Eq (g y) (g z)) (And (Eq (g y) (g z)) (And (Eq (g y) y) (And (Eq (f x) x) (And (Eq (f z) z) (And (Eq (g z) z) (Or (Not (Eq x z)) (Not (Eq y z))))))))))) → False :=
fun lean_r0 : (Eq (Not (Not (Eq x y))) (Eq x y)) =>
fun lean_r1 : (Eq (Eq (Not (Not (Eq x y))) (Eq x y)) (Eq (Eq x y) (Not (Not (Eq x y))))) =>
fun lean_r2 : (Eq (Eq (f z) z) (Eq z (f z))) =>
fun lean_r3 : (Eq (Eq (g z) z) (Eq z (g z))) =>
fun lean_r4 : (Eq (Eq (f x) x) (Eq x (f x))) =>
fun lean_r5 : (Eq (Eq (Eq x y) (Eq x y)) True) =>
fun lean_r6 : (Eq (Eq (g y) y) (Eq y (g y))) =>
fun lean_a7 : (And (Not (Eq x y)) (And (Eq (f x) (f z)) (And (Eq (g y) (g z)) (And (Eq (g y) (g z)) (And (Eq (g y) y) (And (Eq (f x) x) (And (Eq (f z) z) (And (Eq (g z) z) (Or (Not (Eq x z)) (Not (Eq y z))))))))))) => by
have lean_s0 : (Or (And (Not (Eq x y)) (And (Eq x (f x)) (And (Eq (f x) (f z)) (And (Eq z (f z)) (And (Eq y (g y)) (Eq (g y) (g z))))))) (Or (Not (Not (Eq x y))) (Or (Not (Eq x (f x))) (Or (Not (Eq (f x) (f z))) (Or (Not (Eq z (f z))) (Or (Not (Eq y (g y))) (Not (Eq (g y) (g z))))))))) := cnfAndNeg [(Not (Eq x y)), (Eq x (f x)), (Eq (f x) (f z)), (Eq z (f z)), (Eq y (g y)), (Eq (g y) (g z))]
have lean_s1 : (Or (Not (Not (Eq x y))) (Or (Not (Eq x (f x))) (Or (Not (Eq (f x) (f z))) (Or (Not (Eq z (f z))) (Or (Not (Eq y (g y))) (Or (Not (Eq (g y) (g z))) (Not (Eq z (g z))))))))) :=
  (scope (fun lean_a8 : (Not (Eq x y)) =>
    (scope (fun lean_a9 : (Eq x (f x)) =>
      (scope (fun lean_a10 : (Eq (f x) (f z)) =>
        (scope (fun lean_a11 : (Eq z (f z)) =>
          (scope (fun lean_a12 : (Eq y (g y)) =>
            (scope (fun lean_a13 : (Eq (g y) (g z)) =>
              have lean_s1 : (Eq (f z) z) := Eq.symm lean_a11
              have lean_s2 : (Eq z (f z)) := Eq.symm lean_s1
              have lean_s3 : (Eq (f z) (f x)) := Eq.symm lean_a10
              let lean_s4 := Eq.trans lean_s2 lean_s3
              have lean_s5 : (Eq (f x) x) := Eq.symm lean_a9
              have lean_s6 : (Eq z x) := Eq.trans lean_s4 lean_s5
              let lean_s7 := flipCongrArg lean_s6 [Eq]
              have lean_s8 : (Eq (g z) (g y)) := Eq.symm lean_a13
              have lean_s9 : (Eq (g y) y) := Eq.symm lean_a12
              have lean_s10 : (Eq (g z) y) := Eq.trans lean_s8 lean_s9
              have lean_s11 : (Eq (Eq z (g z)) (Eq x y)) := congr lean_s7 lean_s10
              have lean_s12 : (Eq (Eq x y) False) := falseIntro lean_a8
              have lean_s13 : (Eq (Eq z (g z)) False) := Eq.trans lean_s11 lean_s12
              have lean_s14 : (Not (Eq z (g z))) := falseElim lean_s13
              show (Not (Eq z (g z))) from lean_s14
  ))))))))))))
have lean_s2 : (Implies (And (Not (Eq x y)) (And (Eq x (f x)) (And (Eq (f x) (f z)) (And (Eq z (f z)) (And (Eq y (g y)) (Eq (g y) (g z))))))) (Not (Eq z (g z)))) := by liftOrNToImp lean_s1, 6
have lean_s3 : (Or (Not (And (Not (Eq x y)) (And (Eq x (f x)) (And (Eq (f x) (f z)) (And (Eq z (f z)) (And (Eq y (g y)) (Eq (g y) (g z)))))))) (Not (Eq z (g z)))) := impliesElim lean_s2
have lean_s4 : (Or (Not (Not (Eq x y))) (Or (Not (Eq x (f x))) (Or (Not (Eq (f x) (f z))) (Or (Not (Eq z (f z))) (Or (Not (Eq y (g y))) (Or (Not (Eq (g y) (g z))) (Not (Eq z (g z))))))))) := by R1 lean_s0, lean_s3, (And (Not (Eq x y)) (And (Eq x (f x)) (And (Eq (f x) (f z)) (And (Eq z (f z)) (And (Eq y (g y)) (Eq (g y) (g z))))))), [(- 1), (- 1)]
have lean_s5 : (Eq Or Or) := rfl
have lean_s6 : (Eq (Eq x y) (Eq x y)) := rfl
let lean_s7 := flipCongrArg lean_s6 [Eq]
have lean_s8 : (Eq (Eq (Eq x y) (Not (Not (Eq x y)))) (Eq (Eq x y) (Eq x y))) := congr lean_s7 lean_r0
have lean_s9 : (Eq (Eq (Eq x y) (Not (Not (Eq x y)))) True) := Eq.trans lean_s8 lean_r5
have lean_s10 : (Eq (Eq (Not (Not (Eq x y))) (Eq x y)) True) := Eq.trans lean_r1 lean_s9
have lean_s11 : (Eq (Not (Not (Eq x y))) (Eq x y)) := trueElim lean_s10
let lean_s12 := congr lean_s5 lean_s11
have lean_s13 : (Eq (Not (Eq x (f x))) (Not (Eq x (f x)))) := rfl
let lean_s14 := congr lean_s5 lean_s13
have lean_s15 : (Eq (Not (Eq (f x) (f z))) (Not (Eq (f x) (f z)))) := rfl
let lean_s16 := congr lean_s5 lean_s15
have lean_s17 : (Eq (Not (Eq z (f z))) (Not (Eq z (f z)))) := rfl
let lean_s18 := congr lean_s5 lean_s17
have lean_s19 : (Eq (Not (Eq y (g y))) (Not (Eq y (g y)))) := rfl
let lean_s20 := congr lean_s5 lean_s19
have lean_s21 : (Eq (Not (Eq (g y) (g z))) (Not (Eq (g y) (g z)))) := rfl
let lean_s22 := congr lean_s5 lean_s21
have lean_s23 : (Eq (Not (Eq z (g z))) (Not (Eq z (g z)))) := rfl
let lean_s24 := congr lean_s22 lean_s23
let lean_s25 := congr lean_s20 lean_s24
let lean_s26 := congr lean_s18 lean_s25
let lean_s27 := congr lean_s16 lean_s26
let lean_s28 := congr lean_s14 lean_s27
have lean_s29 : (Eq (Or (Not (Not (Eq x y))) (Or (Not (Eq x (f x))) (Or (Not (Eq (f x) (f z))) (Or (Not (Eq z (f z))) (Or (Not (Eq y (g y))) (Or (Not (Eq (g y) (g z))) (Not (Eq z (g z))))))))) (Or (Eq x y) (Or (Not (Eq x (f x))) (Or (Not (Eq (f x) (f z))) (Or (Not (Eq z (f z))) (Or (Not (Eq y (g y))) (Or (Not (Eq (g y) (g z))) (Not (Eq z (g z)))))))))) := congr lean_s12 lean_s28
have lean_s30 : (Or (Eq x y) (Or (Not (Eq x (f x))) (Or (Not (Eq (f x) (f z))) (Or (Not (Eq z (f z))) (Or (Not (Eq y (g y))) (Or (Not (Eq (g y) (g z))) (Not (Eq z (g z))))))))) := eqResolve lean_s4 lean_s29
have lean_s31 : (Or (Eq x y) (Or (Not (Eq (f x) (f z))) (Or (Not (Eq (g y) (g z))) (Or (Not (Eq y (g y))) (Or (Not (Eq x (f x))) (Or (Not (Eq z (f z))) (Not (Eq z (g z))))))))) := by permutateOr lean_s30, [0, 2, 5, 4, 1, 3, 6], (- 1)
have lean_s32 : (Eq And And) := rfl
have lean_s33 : (Eq (Not (Eq x y)) (Not (Eq x y))) := rfl
let lean_s34 := congr lean_s32 lean_s33
have lean_s35 : (Eq (Eq (f x) (f z)) (Eq (f x) (f z))) := rfl
let lean_s36 := congr lean_s32 lean_s35
have lean_s37 : (Eq (Eq (g y) (g z)) (Eq (g y) (g z))) := rfl
let lean_s38 := congr lean_s32 lean_s37
let lean_s39 := congr lean_s32 lean_s37
let lean_s40 := congr lean_s32 lean_r6
let lean_s41 := congr lean_s32 lean_r4
let lean_s42 := congr lean_s32 lean_r2
let lean_s43 := congr lean_s32 lean_r3
have lean_s44 : (Eq (Or (Not (Eq x z)) (Not (Eq y z))) (Or (Not (Eq x z)) (Not (Eq y z)))) := rfl
let lean_s45 := congr lean_s43 lean_s44
let lean_s46 := congr lean_s42 lean_s45
let lean_s47 := congr lean_s41 lean_s46
let lean_s48 := congr lean_s40 lean_s47
let lean_s49 := congr lean_s39 lean_s48
let lean_s50 := congr lean_s38 lean_s49
let lean_s51 := congr lean_s36 lean_s50
have lean_s52 : (Eq (And (Not (Eq x y)) (And (Eq (f x) (f z)) (And (Eq (g y) (g z)) (And (Eq (g y) (g z)) (And (Eq (g y) y) (And (Eq (f x) x) (And (Eq (f z) z) (And (Eq (g z) z) (Or (Not (Eq x z)) (Not (Eq y z))))))))))) (And (Not (Eq x y)) (And (Eq (f x) (f z)) (And (Eq (g y) (g z)) (And (Eq (g y) (g z)) (And (Eq y (g y)) (And (Eq x (f x)) (And (Eq z (f z)) (And (Eq z (g z)) (Or (Not (Eq x z)) (Not (Eq y z)))))))))))) := congr lean_s34 lean_s51
have lean_s53 : (And (Not (Eq x y)) (And (Eq (f x) (f z)) (And (Eq (g y) (g z)) (And (Eq (g y) (g z)) (And (Eq y (g y)) (And (Eq x (f x)) (And (Eq z (f z)) (And (Eq z (g z)) (Or (Not (Eq x z)) (Not (Eq y z))))))))))) := eqResolve lean_a7 lean_s52
have lean_s54 : (Eq z (g z)) := by andElim lean_s53, 7
let lean_s55 := by R2 lean_s31, lean_s54, (Eq z (g z)), [(- 1), 0]
have lean_s56 : (Eq z (f z)) := by andElim lean_s53, 6
let lean_s57 := by R2 lean_s55, lean_s56, (Eq z (f z)), [(- 1), 0]
have lean_s58 : (Eq x (f x)) := by andElim lean_s53, 5
let lean_s59 := by R2 lean_s57, lean_s58, (Eq x (f x)), [(- 1), 0]
have lean_s60 : (Eq y (g y)) := by andElim lean_s53, 4
let lean_s61 := by R2 lean_s59, lean_s60, (Eq y (g y)), [(- 1), 0]
have lean_s62 : (Eq (g y) (g z)) := by andElim lean_s53, 2
let lean_s63 := by R2 lean_s61, lean_s62, (Eq (g y) (g z)), [(- 1), 0]
have lean_s64 : (Eq (f x) (f z)) := by andElim lean_s53, 1
let lean_s65 := by R2 lean_s63, lean_s64, (Eq (f x) (f z)), [(- 1), 0]
have lean_s66 : (Not (Eq x y)) := by andElim lean_s53, 0
exact (show False from by R1 lean_s65, lean_s66, (Eq x y), [0, 0])
