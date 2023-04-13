import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {B : Type u} [Nonempty B]
variable {A : Type u} [Nonempty A]
variable {b : A}
variable {y : A}
variable {a : A}
variable {f : (A -> B)}
variable {x : A}
variable {x : A}
variable {f : (A -> B)}
variable {y : A}
variable {b : A}
variable {a : A}

theorem th0 : (Eq (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) (And (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) (Implies (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) (Eq x y)))) → (Eq (Eq (Not (Not (Eq y a))) (Eq y a)) (Eq (Eq y a) (Not (Not (Eq y a))))) → (Eq (Eq (Eq y a) (Eq y a)) True) → (Eq (Not (Not (Eq y a))) (Eq y a)) → (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) → (Not (Eq (f x) (f y))) → False :=
fun lean_h0 : (Eq (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) (And (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) (Implies (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) (Eq x y)))) =>
fun lean_r1 : (Eq (Eq (Not (Not (Eq y a))) (Eq y a)) (Eq (Eq y a) (Not (Not (Eq y a))))) =>
fun lean_r2 : (Eq (Eq (Eq y a) (Eq y a)) True) =>
fun lean_r3 : (Eq (Not (Not (Eq y a))) (Eq y a)) =>
fun lean_a4 : (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) =>
fun lean_a5 : (Not (Eq (f x) (f y))) => by
have lean_s0 : (Or (And (Eq x b) (Eq y b)) (Or (Not (Eq x b)) (Not (Eq y b)))) := cnfAndNeg [(Eq x b), (Eq y b)]
have lean_s1 : (Or (Not (Eq x b)) (Or (Not (Eq y b)) (Eq (f x) (f y)))) :=
  (scope (fun lean_a6 : (Eq x b) =>
    (scope (fun lean_a7 : (Eq y b) =>
      have lean_s1 : (And (Eq y b) (Eq x b)) := And.intro lean_a7 lean_a6
      have lean_s2 : (Or (Not (Eq y b)) (Or (Not (Eq x b)) (Eq (f x) (f y)))) :=
        (scope (fun lean_a8 : (Eq y b) =>
          (scope (fun lean_a9 : (Eq x b) =>
            have lean_s2 : (Eq b x) := Eq.symm lean_a9
            have lean_s3 : (Eq x b) := Eq.symm lean_s2
            have lean_s4 : (Eq b y) := Eq.symm lean_a8
            have lean_s5 : (Eq x y) := Eq.trans lean_s3 lean_s4
            have lean_s6 : (Eq (f x) (f y)) := flipCongrArg lean_s5 [f]
            show (Eq (f x) (f y)) from lean_s6
        ))))
      have lean_s3 : (Implies (And (Eq y b) (Eq x b)) (Eq (f x) (f y))) := by liftOrNToImp lean_s2, 2
      have lean_s4 : (Eq (f x) (f y)) := modusPonens lean_s1 lean_s3
      show (Eq (f x) (f y)) from lean_s4
  ))))
have lean_s2 : (Implies (And (Eq x b) (Eq y b)) (Eq (f x) (f y))) := by liftOrNToImp lean_s1, 2
have lean_s3 : (Or (Not (And (Eq x b) (Eq y b))) (Eq (f x) (f y))) := impliesElim lean_s2
have lean_s4 : (Or (Not (Eq x b)) (Or (Not (Eq y b)) (Eq (f x) (f y)))) := by R1 lean_s0, lean_s3, (And (Eq x b) (Eq y b)), [(- 1), (- 1)]
have lean_s5 : (Or (Eq (f x) (f y)) (Or (Not (Eq x b)) (Not (Eq y b)))) := by permutateOr lean_s4, [2, 0, 1], (- 1)
have lean_s6 : (Or (Not (And (Eq x b) (Eq y b))) (Eq y b)) := @cnfAndPos [(Eq x b), (Eq y b)] 1
have lean_s7 : (Or (Eq y b) (Not (And (Eq x b) (Eq y b)))) := by permutateOr lean_s6, [1, 0], (- 1)
have lean_s8 : (And (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) (Implies (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) (Eq x y))) := eqResolve lean_a4 lean_h0
have lean_s9 : (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) := by andElim lean_s8, 0
have lean_s10 : (Or (Not (And (Eq x a) (Eq y a))) (Eq x a)) := @cnfAndPos [(Eq x a), (Eq y a)] 0
have lean_s11 : (Or (Eq x a) (Not (And (Eq x a) (Eq y a)))) := by permutateOr lean_s10, [1, 0], (- 1)
have lean_s12 : (Or (And (Eq x a) (And (Eq x b) (Not (Eq y a)))) (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Not (Not (Eq y a)))))) := cnfAndNeg [(Eq x a), (Eq x b), (Not (Eq y a))]
have lean_s13 : (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Or (Not (Not (Eq y a))) (Not (Eq y b))))) :=
  (scope (fun lean_a8 : (Eq x a) =>
    (scope (fun lean_a9 : (Eq x b) =>
      (scope (fun lean_a10 : (Not (Eq y a)) =>
        let lean_s13 := And.intro lean_a8 lean_a9
        have lean_s14 : (And (Not (Eq y a)) (And (Eq x a) (Eq x b))) := And.intro lean_a10 lean_s13
        have lean_s15 : (Or (Not (Not (Eq y a))) (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Not (Eq y b))))) :=
          (scope (fun lean_a10 : (Not (Eq y a)) =>
            (scope (fun lean_a11 : (Eq x a) =>
              (scope (fun lean_a12 : (Eq x b) =>
                have lean_s15 : (Eq y y) := rfl
                let lean_s16 := flipCongrArg lean_s15 [Eq]
                have lean_s17 : (Eq b x) := Eq.symm lean_a12
                have lean_s18 : (Eq a x) := Eq.symm lean_a11
                have lean_s19 : (Eq x a) := Eq.symm lean_s18
                have lean_s20 : (Eq b a) := Eq.trans lean_s17 lean_s19
                have lean_s21 : (Eq (Eq y b) (Eq y a)) := congr lean_s16 lean_s20
                have lean_s22 : (Eq (Eq y a) False) := falseIntro lean_a10
                have lean_s23 : (Eq (Eq y b) False) := Eq.trans lean_s21 lean_s22
                have lean_s24 : (Not (Eq y b)) := falseElim lean_s23
                show (Not (Eq y b)) from lean_s24
          ))))))
        have lean_s16 : (Implies (And (Not (Eq y a)) (And (Eq x a) (Eq x b))) (Not (Eq y b))) := by liftOrNToImp lean_s15, 3
        have lean_s17 : (Not (Eq y b)) := modusPonens lean_s14 lean_s16
        show (Not (Eq y b)) from lean_s17
  ))))))
have lean_s14 : (Implies (And (Eq x a) (And (Eq x b) (Not (Eq y a)))) (Not (Eq y b))) := by liftOrNToImp lean_s13, 3
have lean_s15 : (Or (Not (And (Eq x a) (And (Eq x b) (Not (Eq y a))))) (Not (Eq y b))) := impliesElim lean_s14
have lean_s16 : (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Or (Not (Not (Eq y a))) (Not (Eq y b))))) := by R1 lean_s12, lean_s15, (And (Eq x a) (And (Eq x b) (Not (Eq y a)))), [(- 1), (- 1)]
have lean_s17 : (Eq Or Or) := rfl
have lean_s18 : (Eq (Not (Eq x a)) (Not (Eq x a))) := rfl
let lean_s19 := congr lean_s17 lean_s18
have lean_s20 : (Eq (Not (Eq x b)) (Not (Eq x b))) := rfl
let lean_s21 := congr lean_s17 lean_s20
have lean_s22 : (Eq (Eq y a) (Eq y a)) := rfl
let lean_s23 := flipCongrArg lean_s22 [Eq]
have lean_s24 : (Eq (Eq (Eq y a) (Not (Not (Eq y a)))) (Eq (Eq y a) (Eq y a))) := congr lean_s23 lean_r3
have lean_s25 : (Eq (Eq (Eq y a) (Not (Not (Eq y a)))) True) := Eq.trans lean_s24 lean_r2
have lean_s26 : (Eq (Eq (Not (Not (Eq y a))) (Eq y a)) True) := Eq.trans lean_r1 lean_s25
have lean_s27 : (Eq (Not (Not (Eq y a))) (Eq y a)) := trueElim lean_s26
let lean_s28 := congr lean_s17 lean_s27
have lean_s29 : (Eq (Not (Eq y b)) (Not (Eq y b))) := rfl
let lean_s30 := congr lean_s28 lean_s29
let lean_s31 := congr lean_s21 lean_s30
have lean_s32 : (Eq (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Or (Not (Not (Eq y a))) (Not (Eq y b))))) (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Or (Eq y a) (Not (Eq y b)))))) := congr lean_s19 lean_s31
have lean_s33 : (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Or (Eq y a) (Not (Eq y b))))) := eqResolve lean_s16 lean_s32
have lean_s34 : (Or (Eq y a) (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Not (Eq y b))))) := by permutateOr lean_s33, [2, 0, 1, 3], (- 1)
let lean_s35 := by R2 lean_s34, lean_s7, (Eq y b), [(- 1), (- 1)]
have lean_s36 : (Or (Not (And (Eq x b) (Eq y b))) (Eq x b)) := @cnfAndPos [(Eq x b), (Eq y b)] 0
have lean_s37 : (Or (Eq x b) (Not (And (Eq x b) (Eq y b)))) := by permutateOr lean_s36, [1, 0], (- 1)
have lean_s38 : (Or (Eq y a) (Or (Not (Eq x a)) (Or (Not (And (Eq x b) (Eq y b))) (Not (And (Eq x b) (Eq y b)))))) := by R2 lean_s35, lean_s37, (Eq x b), [(- 1), (- 1)]
have lean_s39 : (Or (Eq y a) (Or (Not (Eq x a)) (Not (And (Eq x b) (Eq y b))))) := by factor lean_s38, (- 1)
let lean_s40 := by R2 lean_s39, lean_s9, (And (Eq x b) (Eq y b)), [(- 1), (- 1)]
have lean_s41 : (Or (Not (And (Eq x a) (Eq y a))) (Eq y a)) := @cnfAndPos [(Eq x a), (Eq y a)] 1
have lean_s42 : (Or (Eq y a) (Not (And (Eq x a) (Eq y a)))) := by permutateOr lean_s41, [1, 0], (- 1)
have lean_s43 : (Or (Eq y a) (Or (Not (Eq x a)) (Eq y a))) := by R1 lean_s40, lean_s42, (And (Eq x a) (Eq y a)), [(- 1), (- 1)]
have lean_s44 : (Or (Eq y a) (Not (Eq x a))) := by factor lean_s43, 2
have lean_s45 : (Or (And (Eq x a) (Eq y a)) (Or (Not (Eq x a)) (Not (Eq y a)))) := cnfAndNeg [(Eq x a), (Eq y a)]
have lean_s46 : (Or (Not (Eq x a)) (Or (Not (Eq y a)) (Eq (f x) (f y)))) :=
  (scope (fun lean_a10 : (Eq x a) =>
    (scope (fun lean_a11 : (Eq y a) =>
      have lean_s46 : (And (Eq y a) (Eq x a)) := And.intro lean_a11 lean_a10
      have lean_s47 : (Or (Not (Eq y a)) (Or (Not (Eq x a)) (Eq (f x) (f y)))) :=
        (scope (fun lean_a11 : (Eq y a) =>
          (scope (fun lean_a12 : (Eq x a) =>
            have lean_s47 : (Eq a x) := Eq.symm lean_a12
            have lean_s48 : (Eq x a) := Eq.symm lean_s47
            have lean_s49 : (Eq a y) := Eq.symm lean_a11
            have lean_s50 : (Eq x y) := Eq.trans lean_s48 lean_s49
            have lean_s51 : (Eq (f x) (f y)) := flipCongrArg lean_s50 [f]
            show (Eq (f x) (f y)) from lean_s51
        ))))
      have lean_s48 : (Implies (And (Eq y a) (Eq x a)) (Eq (f x) (f y))) := by liftOrNToImp lean_s47, 2
      have lean_s49 : (Eq (f x) (f y)) := modusPonens lean_s46 lean_s48
      show (Eq (f x) (f y)) from lean_s49
  ))))
have lean_s47 : (Implies (And (Eq x a) (Eq y a)) (Eq (f x) (f y))) := by liftOrNToImp lean_s46, 2
have lean_s48 : (Or (Not (And (Eq x a) (Eq y a))) (Eq (f x) (f y))) := impliesElim lean_s47
have lean_s49 : (Or (Not (Eq x a)) (Or (Not (Eq y a)) (Eq (f x) (f y)))) := by R1 lean_s45, lean_s48, (And (Eq x a) (Eq y a)), [(- 1), (- 1)]
have lean_s50 : (Or (Eq (f x) (f y)) (Or (Not (Eq x a)) (Not (Eq y a)))) := by permutateOr lean_s49, [2, 0, 1], (- 1)
let lean_s51 := by R1 lean_s44, lean_s50, (Eq y a), [(- 1), (- 1)]
have lean_s52 : (Or (Not (Eq x a)) (Not (Eq x a))) := by R1 lean_s51, lean_a5, (Eq (f x) (f y)), [(- 1), 0]
have lean_s53 : (Not (Eq x a)) := by factor lean_s52, 1
have lean_s54 : (Not (And (Eq x a) (Eq y a))) := by R1 lean_s11, lean_s53, (Eq x a), [(- 1), 0]
have lean_s55 : (And (Eq x b) (Eq y b)) := by R1 lean_s9, lean_s54, (And (Eq x a) (Eq y a)), [(- 1), 0]
have lean_s56 : (Eq y b) := by R2 lean_s7, lean_s55, (And (Eq x b) (Eq y b)), [(- 1), 0]
let lean_s57 := by R2 lean_s5, lean_s56, (Eq y b), [(- 1), 0]
have lean_s58 : (Eq x b) := by R2 lean_s37, lean_s55, (And (Eq x b) (Eq y b)), [(- 1), 0]
let lean_s59 := by R2 lean_s57, lean_s58, (Eq x b), [(- 1), 0]
exact (show False from by R1 lean_s59, lean_a5, (Eq (f x) (f y)), [0, 0])
