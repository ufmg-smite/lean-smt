import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {U : Type u} [Nonempty U]
variable {y : U}
variable {z : U}
variable {H : (U -> U -> U)}
variable {x : U}
variable {J : (U -> U -> U)}
variable {f : (U -> U)}
variable {x : U}
variable {H : (U -> U -> U)}
variable {J : (U -> U -> U)}
variable {f : (U -> U)}
variable {y : U}
variable {z : U}

theorem th0 : (Eq (Eq (Not (Not (Eq x (J z y)))) (Eq x (J z y))) (Eq (Eq x (J z y)) (Not (Not (Eq x (J z y)))))) → (Eq (Eq (Eq x (J z y)) (Eq x (J z y))) True) → (Eq (Not (Not (Eq x (J z y)))) (Eq x (J z y))) → (And (Eq (H x y) (H y x)) (And (Or (Eq x (J z y)) (Eq y (J z y))) (And (Eq (J z y) (f x)) (And (Or (Eq x (f x)) (Not (Eq y (f x)))) (Or (Not (Eq x (f x))) (Not (Eq (H x (f x)) (H (f x) x)))))))) → False :=
fun lean_r0 : (Eq (Eq (Not (Not (Eq x (J z y)))) (Eq x (J z y))) (Eq (Eq x (J z y)) (Not (Not (Eq x (J z y)))))) =>
fun lean_r1 : (Eq (Eq (Eq x (J z y)) (Eq x (J z y))) True) =>
fun lean_r2 : (Eq (Not (Not (Eq x (J z y)))) (Eq x (J z y))) =>
fun lean_a3 : (And (Eq (H x y) (H y x)) (And (Or (Eq x (J z y)) (Eq y (J z y))) (And (Eq (J z y) (f x)) (And (Or (Eq x (f x)) (Not (Eq y (f x)))) (Or (Not (Eq x (f x))) (Not (Eq (H x (f x)) (H (f x) x)))))))) => by
have lean_s0 : (Or (Not (Eq x (f x))) (Not (Eq (H x (f x)) (H (f x) x)))) := by andElim lean_a3, 4
have lean_s1 : (Or (And (Eq (J z y) (f x)) (Eq x (J z y))) (Or (Not (Eq (J z y) (f x))) (Not (Eq x (J z y))))) := cnfAndNeg [(Eq (J z y) (f x)), (Eq x (J z y))]
have lean_s2 : (Or (Not (Eq (J z y) (f x))) (Or (Not (Eq x (J z y))) (Eq (H x (f x)) (H (f x) x)))) :=
  (scope (fun lean_a4 : (Eq (J z y) (f x)) =>
    (scope (fun lean_a5 : (Eq x (J z y)) =>
      have lean_s2 : (Eq (f x) (J z y)) := Eq.symm lean_a4
      have lean_s3 : (Eq (J z y) x) := Eq.symm lean_a5
      have lean_s4 : (Eq (f x) x) := Eq.trans lean_s2 lean_s3
      have lean_s5 : (Eq x (f x)) := Eq.symm lean_s4
      let lean_s6 := flipCongrArg lean_s5 [H]
      have lean_s7 : (Eq (H x (f x)) (H (f x) x)) := congr lean_s6 lean_s4
      show (Eq (H x (f x)) (H (f x) x)) from lean_s7
  ))))
have lean_s3 : (Implies (And (Eq (J z y) (f x)) (Eq x (J z y))) (Eq (H x (f x)) (H (f x) x))) := by liftOrNToImp lean_s2, 2
have lean_s4 : (Or (Not (And (Eq (J z y) (f x)) (Eq x (J z y)))) (Eq (H x (f x)) (H (f x) x))) := impliesElim lean_s3
have lean_s5 : (Or (Not (Eq (J z y) (f x))) (Or (Not (Eq x (J z y))) (Eq (H x (f x)) (H (f x) x)))) := by R1 lean_s1, lean_s4, (And (Eq (J z y) (f x)) (Eq x (J z y))), [(- 1), (- 1)]
have lean_s6 : (Or (Eq (H x (f x)) (H (f x) x)) (Or (Not (Eq x (J z y))) (Not (Eq (J z y) (f x))))) := by permutateOr lean_s5, [2, 1, 0], (- 1)
have lean_s7 : (Or (Eq x (f x)) (Not (Eq y (f x)))) := by andElim lean_a3, 3
have lean_s8 : (Or (And (Eq (J z y) (f x)) (Eq y (J z y))) (Or (Not (Eq (J z y) (f x))) (Not (Eq y (J z y))))) := cnfAndNeg [(Eq (J z y) (f x)), (Eq y (J z y))]
have lean_s9 : (Or (Not (Eq (J z y) (f x))) (Or (Not (Eq y (J z y))) (Eq y (f x)))) :=
  (scope (fun lean_a6 : (Eq (J z y) (f x)) =>
    (scope (fun lean_a7 : (Eq y (J z y)) =>
      have lean_s9 : (Eq (J z y) y) := Eq.symm lean_a7
      have lean_s10 : (Eq y (J z y)) := Eq.symm lean_s9
      have lean_s11 : (Eq (f x) (J z y)) := Eq.symm lean_a6
      have lean_s12 : (Eq (J z y) (f x)) := Eq.symm lean_s11
      have lean_s13 : (Eq y (f x)) := Eq.trans lean_s10 lean_s12
      show (Eq y (f x)) from lean_s13
  ))))
have lean_s10 : (Implies (And (Eq (J z y) (f x)) (Eq y (J z y))) (Eq y (f x))) := by liftOrNToImp lean_s9, 2
have lean_s11 : (Or (Not (And (Eq (J z y) (f x)) (Eq y (J z y)))) (Eq y (f x))) := impliesElim lean_s10
have lean_s12 : (Or (Not (Eq (J z y) (f x))) (Or (Not (Eq y (J z y))) (Eq y (f x)))) := by R1 lean_s8, lean_s11, (And (Eq (J z y) (f x)) (Eq y (J z y))), [(- 1), (- 1)]
have lean_s13 : (Or (Eq y (f x)) (Or (Not (Eq y (J z y))) (Not (Eq (J z y) (f x))))) := by permutateOr lean_s12, [2, 1, 0], (- 1)
let lean_s14 := by R2 lean_s7, lean_s13, (Eq y (f x)), [(- 1), (- 1)]
have lean_s15 : (Eq (J z y) (f x)) := by andElim lean_a3, 2
let lean_s16 := by R2 lean_s14, lean_s15, (Eq (J z y) (f x)), [(- 1), 0]
have lean_s17 : (Or (And (Not (Eq x (J z y))) (Eq (J z y) (f x))) (Or (Not (Not (Eq x (J z y)))) (Not (Eq (J z y) (f x))))) := cnfAndNeg [(Not (Eq x (J z y))), (Eq (J z y) (f x))]
have lean_s18 : (Or (Not (Not (Eq x (J z y)))) (Or (Not (Eq (J z y) (f x))) (Not (Eq x (f x))))) :=
  (scope (fun lean_a7 : (Not (Eq x (J z y))) =>
    (scope (fun lean_a8 : (Eq (J z y) (f x)) =>
      have lean_s18 : (Eq x x) := rfl
      let lean_s19 := flipCongrArg lean_s18 [Eq]
      have lean_s20 : (Eq (f x) (J z y)) := Eq.symm lean_a8
      have lean_s21 : (Eq (J z y) (f x)) := Eq.symm lean_s20
      have lean_s22 : (Eq (f x) (J z y)) := Eq.symm lean_s21
      have lean_s23 : (Eq (Eq x (f x)) (Eq x (J z y))) := congr lean_s19 lean_s22
      have lean_s24 : (Eq (Eq x (J z y)) False) := falseIntro lean_a7
      have lean_s25 : (Eq (Eq x (f x)) False) := Eq.trans lean_s23 lean_s24
      have lean_s26 : (Not (Eq x (f x))) := falseElim lean_s25
      show (Not (Eq x (f x))) from lean_s26
  ))))
have lean_s19 : (Implies (And (Not (Eq x (J z y))) (Eq (J z y) (f x))) (Not (Eq x (f x)))) := by liftOrNToImp lean_s18, 2
have lean_s20 : (Or (Not (And (Not (Eq x (J z y))) (Eq (J z y) (f x)))) (Not (Eq x (f x)))) := impliesElim lean_s19
have lean_s21 : (Or (Not (Not (Eq x (J z y)))) (Or (Not (Eq (J z y) (f x))) (Not (Eq x (f x))))) := by R1 lean_s17, lean_s20, (And (Not (Eq x (J z y))) (Eq (J z y) (f x))), [(- 1), (- 1)]
have lean_s22 : (Eq Or Or) := rfl
have lean_s23 : (Eq (Eq x (J z y)) (Eq x (J z y))) := rfl
let lean_s24 := flipCongrArg lean_s23 [Eq]
have lean_s25 : (Eq (Eq (Eq x (J z y)) (Not (Not (Eq x (J z y))))) (Eq (Eq x (J z y)) (Eq x (J z y)))) := congr lean_s24 lean_r2
have lean_s26 : (Eq (Eq (Eq x (J z y)) (Not (Not (Eq x (J z y))))) True) := Eq.trans lean_s25 lean_r1
have lean_s27 : (Eq (Eq (Not (Not (Eq x (J z y)))) (Eq x (J z y))) True) := Eq.trans lean_r0 lean_s26
have lean_s28 : (Eq (Not (Not (Eq x (J z y)))) (Eq x (J z y))) := trueElim lean_s27
let lean_s29 := congr lean_s22 lean_s28
have lean_s30 : (Eq (Not (Eq (J z y) (f x))) (Not (Eq (J z y) (f x)))) := rfl
let lean_s31 := congr lean_s22 lean_s30
have lean_s32 : (Eq (Not (Eq x (f x))) (Not (Eq x (f x)))) := rfl
let lean_s33 := congr lean_s31 lean_s32
have lean_s34 : (Eq (Or (Not (Not (Eq x (J z y)))) (Or (Not (Eq (J z y) (f x))) (Not (Eq x (f x))))) (Or (Eq x (J z y)) (Or (Not (Eq (J z y) (f x))) (Not (Eq x (f x)))))) := congr lean_s29 lean_s33
have lean_s35 : (Or (Eq x (J z y)) (Or (Not (Eq (J z y) (f x))) (Not (Eq x (f x))))) := eqResolve lean_s21 lean_s34
have lean_s36 : (Or (Eq x (J z y)) (Or (Not (Eq x (f x))) (Not (Eq (J z y) (f x))))) := by permutateOr lean_s35, [0, 2, 1], (- 1)
let lean_s37 := by R1 lean_s16, lean_s36, (Eq x (f x)), [(- 1), (- 1)]
let lean_s38 := by R2 lean_s37, lean_s15, (Eq (J z y) (f x)), [(- 1), 0]
have lean_s39 : (Or (Eq x (J z y)) (Eq y (J z y))) := by andElim lean_a3, 1
have lean_s40 : (Or (Eq x (J z y)) (Eq x (J z y))) := by R2 lean_s38, lean_s39, (Eq y (J z y)), [(- 1), (- 1)]
have lean_s41 : (Eq x (J z y)) := by factor lean_s40, 1
let lean_s42 := by R2 lean_s6, lean_s41, (Eq x (J z y)), [(- 1), 0]
have lean_s43 : (Eq (H x (f x)) (H (f x) x)) := by R2 lean_s42, lean_s15, (Eq (J z y) (f x)), [(- 1), 0]
let lean_s44 := by R2 lean_s0, lean_s43, (Eq (H x (f x)) (H (f x) x)), [(- 1), 0]
have lean_s45 : (Or (Not (Eq (J z y) (f x))) (Or (Not (Eq x (J z y))) (Eq x (f x)))) :=
  (scope (fun lean_a8 : (Eq (J z y) (f x)) =>
    (scope (fun lean_a9 : (Eq x (J z y)) =>
      have lean_s45 : (Eq (J z y) x) := Eq.symm lean_a9
      have lean_s46 : (Eq x (J z y)) := Eq.symm lean_s45
      have lean_s47 : (Eq (f x) (J z y)) := Eq.symm lean_a8
      have lean_s48 : (Eq (J z y) (f x)) := Eq.symm lean_s47
      have lean_s49 : (Eq x (f x)) := Eq.trans lean_s46 lean_s48
      show (Eq x (f x)) from lean_s49
  ))))
have lean_s46 : (Implies (And (Eq (J z y) (f x)) (Eq x (J z y))) (Eq x (f x))) := by liftOrNToImp lean_s45, 2
have lean_s47 : (Or (Not (And (Eq (J z y) (f x)) (Eq x (J z y)))) (Eq x (f x))) := impliesElim lean_s46
have lean_s48 : (Or (Not (Eq (J z y) (f x))) (Or (Not (Eq x (J z y))) (Eq x (f x)))) := by R1 lean_s1, lean_s47, (And (Eq (J z y) (f x)) (Eq x (J z y))), [(- 1), (- 1)]
have lean_s49 : (Or (Eq x (f x)) (Or (Not (Eq x (J z y))) (Not (Eq (J z y) (f x))))) := by permutateOr lean_s48, [2, 1, 0], (- 1)
let lean_s50 := by R2 lean_s49, lean_s41, (Eq x (J z y)), [(- 1), 0]
have lean_s51 : (Eq x (f x)) := by R2 lean_s50, lean_s15, (Eq (J z y) (f x)), [(- 1), 0]
exact (show False from by R2 lean_s44, lean_s51, (Eq x (f x)), [0, 0])
