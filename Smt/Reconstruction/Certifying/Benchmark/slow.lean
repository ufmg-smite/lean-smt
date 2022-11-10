import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.Resolution
import Smt.Reconstruction.Certifying.Factor
import Smt.Reconstruction.Certifying.PermutateOr

set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {B : Type u}
variable {A : Type u}
variable {a : A}
variable {b : A}
variable {x : A}
variable {f : (A -> B)}
variable {y : A}

theorem th0 : (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) → (Not (Eq (f x) (f y))) → (Iff (Iff (Not (Not (Eq y a))) (Eq y a)) (Iff (Eq y a) (Not (Not (Eq y a))))) → (Iff (Not (Not (Eq y a))) (Eq y a)) → (Iff (Iff (Eq y a) (Eq y a)) True) → (Iff (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) (And (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) ((Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) -> (Eq x y)))) → False :=
fun lean_a0 : (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) =>
fun lean_a1 : (Not (Eq (f x) (f y))) =>
fun lean_a2 : (Iff (Iff (Not (Not (Eq y a))) (Eq y a)) (Iff (Eq y a) (Not (Not (Eq y a))))) =>
fun lean_a3 : (Iff (Not (Not (Eq y a))) (Eq y a)) =>
fun lean_a4 : (Iff (Iff (Eq y a) (Eq y a)) True) =>
fun lean_a5 : (Iff (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) (And (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) ((Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) -> (Eq x y)))) => by
have lean_s0 : (Or (And (Eq x b) (Eq y b)) (Or (Not (Eq x b)) (Not (Eq y b)))) := by cnfAndNegT [(Eq x b), (Eq y b)]
have lean_s1 : (Or (Not (Eq x b)) (Or (Not (Eq y b)) (Eq (f x) (f y)))) :=
  (scope (fun lean_a6 : (Eq x b) =>
    (scope (fun lean_a7 : (Eq y b) =>
      have lean_s1 : (And (Eq y b) (Eq x b)) := And.intro lean_a7 lean_a6
      have lean_s2 : (Or (Not (Eq y b)) (Or (Not (Eq x b)) (Eq (f x) (f y)))) :=
        (scope (fun lean_a8 : (Eq y b) =>
          (scope (fun lean_a9 : (Eq x b) =>
            have lean_s2 : (Eq f f) := rfl
            have lean_s3 : (Eq b x) := Eq.symm lean_a9
            have lean_s4 : (Eq x b) := Eq.symm lean_s3
            have lean_s5 : (Eq b y) := Eq.symm lean_a8
            have lean_s6 : (Eq x y) := Eq.trans lean_s4 lean_s5
            have lean_s7 : (Eq (f x) (f y)) := by smtCong lean_s2, lean_s6
            show (Eq (f x) (f y)) from lean_s7
        ))))
      have lean_s3 : ((And (Eq y b) (Eq x b)) -> (Eq (f x) (f y))) := by liftOrNToImp lean_s2, 2
      have lean_s4 : (Eq (f x) (f y)) := modusPonens lean_s1 lean_s3
      show (Eq (f x) (f y)) from lean_s4
  ))))
have lean_s2 : ((And (Eq x b) (Eq y b)) -> (Eq (f x) (f y))) := by liftOrNToImp lean_s1, 2
clear lean_s1
have lean_s3 : (Or (Not (And (Eq x b) (Eq y b))) (Eq (f x) (f y))) := impliesElim lean_s2
have lean_s4 : (Or (Not (Eq x b)) (Or (Not (Eq y b)) (Eq (f x) (f y)))) := by R1 lean_s0, lean_s3, (And (Eq x b) (Eq y b))
clear lean_s0
have lean_s5 : (Or (Eq (f x) (f y)) (Or (Not (Eq x b)) (Not (Eq y b)))) := by permutateOr lean_s4, [2, 0, 1]
have lean_s6 : (Or (Not (And (Eq x b) (Eq y b))) (Eq y b)) := by cnfAndPosT [(Eq x b), (Eq y b)], 1
have lean_s7 : (Or (Eq y b) (Not (And (Eq x b) (Eq y b)))) := by permutateOr lean_s6, [1, 0]
have lean_s8 : (And (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) ((Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) -> (Eq x y))) := eqResolve lean_a0 lean_a5
clear lean_a0 lean_a5
have lean_s9 : (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) := by andElim lean_s8, 0
have lean_s10 : (Or (Not (And (Eq x a) (Eq y a))) (Eq x a)) := by cnfAndPosT [(Eq x a), (Eq y a)], 0
have lean_s11 : (Or (Eq x a) (Not (And (Eq x a) (Eq y a)))) := by permutateOr lean_s10, [1, 0]
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
                have lean_s15 : (Eq Eq Eq) := rfl
                have lean_s16 : (Eq y y) := rfl
                let lean_s17 := by smtCong lean_s15, lean_s16
                have lean_s18 : (Eq b x) := Eq.symm lean_a12
                have lean_s19 : (Eq a x) := Eq.symm lean_a11
                have lean_s20 : (Eq x a) := Eq.symm lean_s19
                have lean_s21 : (Eq b a) := Eq.trans lean_s18 lean_s20
                have lean_s22 : (Iff (Eq y b) (Eq y a)) := by smtCong lean_s17, lean_s21
                have lean_s23 : (Iff (Eq y a) False) := falseIntro lean_a10
                have lean_s24 : (Iff (Eq y b) False) := Iff.trans lean_s22 lean_s23
                have lean_s25 : (Not (Eq y b)) := falseElim lean_s24
                show (Not (Eq y b)) from lean_s25
          ))))))
        have lean_s16 : ((And (Not (Eq y a)) (And (Eq x a) (Eq x b))) -> (Not (Eq y b))) := by liftOrNToImp lean_s15, 3
        have lean_s17 : (Not (Eq y b)) := modusPonens lean_s14 lean_s16
        show (Not (Eq y b)) from lean_s17
  ))))))
have lean_s14 : ((And (Eq x a) (And (Eq x b) (Not (Eq y a)))) -> (Not (Eq y b))) := by liftOrNToImp lean_s13, 3
have lean_s15 : (Or (Not (And (Eq x a) (And (Eq x b) (Not (Eq y a))))) (Not (Eq y b))) := impliesElim lean_s14
have lean_s16 : (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Or (Not (Not (Eq y a))) (Not (Eq y b))))) := by R1 lean_s12, lean_s15, (And (Eq x a) (And (Eq x b) (Not (Eq y a))))
have lean_s17 : (Eq Or Or) := rfl
have lean_s18 : (Iff (Not (Eq x a)) (Not (Eq x a))) := Iff.rfl
let lean_s19 := by smtCong lean_s17, lean_s18
have lean_s20 : (Iff (Not (Eq x b)) (Not (Eq x b))) := Iff.rfl
let lean_s21 := by smtCong lean_s17, lean_s20
have lean_s22 : (Eq Iff Iff) := rfl
have lean_s23 : (Iff (Eq y a) (Eq y a)) := Iff.rfl
let lean_s24 := by smtCong lean_s22, lean_s23
have lean_s25 : (Iff (Iff (Eq y a) (Not (Not (Eq y a)))) (Iff (Eq y a) (Eq y a))) := by smtCong lean_s24, lean_a3
clear lean_a3
have lean_s26 : (Iff (Iff (Eq y a) (Not (Not (Eq y a)))) True) := Iff.trans lean_s25 lean_a4
clear lean_a4
have lean_s27 : (Iff (Iff (Not (Not (Eq y a))) (Eq y a)) True) := Iff.trans lean_a2 lean_s26
clear lean_a2
have lean_s28 : (Iff (Not (Not (Eq y a))) (Eq y a)) := trueElim lean_s27
let lean_s29 := by smtCong lean_s17, lean_s28
have lean_s30 : (Iff (Not (Eq y b)) (Not (Eq y b))) := Iff.rfl
let lean_s31 := by smtCong lean_s29, lean_s30
let lean_s32 := by smtCong lean_s21, lean_s31
have lean_s33 : (Iff (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Or (Not (Not (Eq y a))) (Not (Eq y b))))) (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Or (Eq y a) (Not (Eq y b)))))) := by smtCong lean_s19, lean_s32
have lean_s34 : (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Or (Eq y a) (Not (Eq y b))))) := eqResolve lean_s16 lean_s33
have lean_s35 : (Or (Eq y a) (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Not (Eq y b))))) := by permutateOr lean_s34, [2, 0, 1, 3]
let lean_s36 := by R2 lean_s35, lean_s7, (Eq y b)
have lean_s37 : (Or (Not (And (Eq x b) (Eq y b))) (Eq x b)) := by cnfAndPosT [(Eq x b), (Eq y b)], 0
have lean_s38 : (Or (Eq x b) (Not (And (Eq x b) (Eq y b)))) := by permutateOr lean_s37, [1, 0]
have lean_s39 : (Or (Eq y a) (Or (Not (Eq x a)) (Or (Not (And (Eq x b) (Eq y b))) (Not (And (Eq x b) (Eq y b)))))) := by R2 lean_s36, lean_s38, (Eq x b)
have lean_s40 : (Or (Eq y a) (Or (Not (Eq x a)) (Not (And (Eq x b) (Eq y b))))) := by factor lean_s39
let lean_s41 := by R2 lean_s40, lean_s9, (And (Eq x b) (Eq y b))
have lean_s42 : (Or (Not (And (Eq x a) (Eq y a))) (Eq y a)) := by cnfAndPosT [(Eq x a), (Eq y a)], 1
have lean_s43 : (Or (Eq y a) (Not (And (Eq x a) (Eq y a)))) := by permutateOr lean_s42, [1, 0]
have lean_s44 : (Or (Eq y a) (Or (Not (Eq x a)) (Eq y a))) := by R1 lean_s41, lean_s43, (And (Eq x a) (Eq y a))
have lean_s45 : (Or (Eq y a) (Not (Eq x a))) := by factor lean_s44
have lean_s46 : (Or (And (Eq x a) (Eq y a)) (Or (Not (Eq x a)) (Not (Eq y a)))) := by cnfAndNegT [(Eq x a), (Eq y a)]
have lean_s47 : (Or (Not (Eq x a)) (Or (Not (Eq y a)) (Eq (f x) (f y)))) :=
  (scope (fun lean_a10 : (Eq x a) =>
    (scope (fun lean_a11 : (Eq y a) =>
      have lean_s47 : (And (Eq y a) (Eq x a)) := And.intro lean_a11 lean_a10
      have lean_s48 : (Or (Not (Eq y a)) (Or (Not (Eq x a)) (Eq (f x) (f y)))) :=
        (scope (fun lean_a11 : (Eq y a) =>
          (scope (fun lean_a12 : (Eq x a) =>
            have lean_s48 : (Eq f f) := rfl
            have lean_s49 : (Eq a x) := Eq.symm lean_a12
            have lean_s50 : (Eq x a) := Eq.symm lean_s49
            have lean_s51 : (Eq a y) := Eq.symm lean_a11
            have lean_s52 : (Eq x y) := Eq.trans lean_s50 lean_s51
            have lean_s53 : (Eq (f x) (f y)) := by smtCong lean_s48, lean_s52
            show (Eq (f x) (f y)) from lean_s53
        ))))
      have lean_s49 : ((And (Eq y a) (Eq x a)) -> (Eq (f x) (f y))) := by liftOrNToImp lean_s48, 2
      have lean_s50 : (Eq (f x) (f y)) := modusPonens lean_s47 lean_s49
      show (Eq (f x) (f y)) from lean_s50
  ))))
have lean_s48 : ((And (Eq x a) (Eq y a)) -> (Eq (f x) (f y))) := by liftOrNToImp lean_s47, 2
have lean_s49 : (Or (Not (And (Eq x a) (Eq y a))) (Eq (f x) (f y))) := impliesElim lean_s48
have lean_s50 : (Or (Not (Eq x a)) (Or (Not (Eq y a)) (Eq (f x) (f y)))) := by R1 lean_s46, lean_s49, (And (Eq x a) (Eq y a))
have lean_s51 : (Or (Eq (f x) (f y)) (Or (Not (Eq x a)) (Not (Eq y a)))) := by permutateOr lean_s50, [2, 0, 1]
let lean_s52 := by R1 lean_s45, lean_s51, (Eq y a)
have lean_s53 : (Or (Not (Eq x a)) (Not (Eq x a))) := by R1 lean_s52, lean_a1, (Eq (f x) (f y))
have lean_s54 : (Not (Eq x a)) := by factor lean_s53
have lean_s55 : (Not (And (Eq x a) (Eq y a))) := by R1 lean_s11, lean_s54, (Eq x a)
have lean_s56 : (And (Eq x b) (Eq y b)) := by R1 lean_s9, lean_s55, (And (Eq x a) (Eq y a))
have lean_s57 : (Eq y b) := by R2 lean_s7, lean_s56, (And (Eq x b) (Eq y b))
let lean_s58 := by R2 lean_s5, lean_s57, (Eq y b)
have lean_s59 : (Eq x b) := by R2 lean_s38, lean_s56, (And (Eq x b) (Eq y b))
let lean_s60 := by R2 lean_s58, lean_s59, (Eq x b)
exact show False from by R1 lean_s60, lean_a1, (Eq (f x) (f y))
