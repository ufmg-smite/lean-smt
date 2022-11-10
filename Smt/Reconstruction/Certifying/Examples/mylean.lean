
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

/- y = b ∨ ¬(x = b ∧ y = b) -/
/- y = a ∨ ¬x = a ∨ ¬x = b ∨ ¬y = b -/

/- example : y = a ∨ ¬x = a ∨ ¬x = b ∨ ¬y = b → y = b ∨ ¬(x = b ∧ y = b) → (y = a ∨ ¬x = a ∨ ¬x = b) ∨ ¬(x = b ∧ y = b) -/
/-   intros h₁ h₂ -/

-- lean_ss39: (Or (Eq y a) (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Not (Eq y b)))))
-- lean_s7: (Or (Eq y b) (Not (And (Eq x b) (Eq y b))))
-- let lean_s40 := by R2 lean_s39, lean_s7, (Eq y b)

/- example : (Or (Eq y a) (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Not (Eq y b))))) → (Or (Eq y b) (Not (And (Eq x b) (Eq y b)))) → (Or (Eq y a) (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Not (And (Eq x b) (Eq y b)))))) := by -/
/-   intros h1 h2 -/
/-   R2 h1, h2, y = b -/

theorem th0 : (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) → (Not (Eq (f x) (f y))) → False :=
fun lean_a0 : (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) =>
fun lean_a1 : (Not (Eq (f x) (f y))) =>
have lean_s0 : (Or (And (Eq x b) (Eq y b)) (Or (Not (Eq x b)) (Not (Eq y b)))) := cnfAndNeg [(Eq x b), (Eq y b)]
have lean_s1 : (Or (Not (Eq x b)) (Or (Not (Eq y b)) (Eq (f x) (f y)))) :=
  (scope (fun lean_a2 : (Eq x b) =>
    (scope (fun lean_a3 : (Eq y b) =>
      have lean_s1 : (And (Eq y b) (Eq x b)) := And.intro lean_a3 lean_a2
      have lean_s2 : (Or (Not (Eq y b)) (Or (Not (Eq x b)) (Eq (f x) (f y)))) :=
        (scope (fun lean_a4 : (Eq y b) =>
          (scope (fun lean_a5 : (Eq x b) =>
            have lean_s2 : (Eq f f) := rfl
            have lean_s3 : (Eq b x) := Eq.symm lean_a5
            have lean_s4 : (Eq x b) := Eq.symm lean_s3
            have lean_s5 : (Eq b y) := Eq.symm lean_a4
            have lean_s6 : (Eq x y) := Eq.trans lean_s4 lean_s5
            have lean_s7 : (Eq (f x) (f y)) := by smtCong lean_s2, lean_s6
            show (Eq (f x) (f y)) from lean_s7
        ))))
      have lean_s3 : ((And (Eq y b) (Eq x b)) -> (Eq (f x) (f y))) := by liftOrNToImp lean_s2, 2
      have lean_s4 : (Eq (f x) (f y)) := modusPonens lean_s1 lean_s3
      show (Eq (f x) (f y)) from lean_s4
  ))))
have lean_s2 : ((And (Eq x b) (Eq y b)) -> (Eq (f x) (f y))) := by liftOrNToImp lean_s1, 2
have lean_s3 : (Or (Not (And (Eq x b) (Eq y b))) (Eq (f x) (f y))) := impliesElim lean_s2
have lean_s4 : (Or (Not (Eq x b)) (Or (Not (Eq y b)) (Eq (f x) (f y)))) := by R1 lean_s0, lean_s3, (And (Eq x b) (Eq y b))
have lean_s5 : (Or (Eq (f x) (f y)) (Or (Not (Eq x b)) (Not (Eq y b)))) := by permutateOr lean_s4, [2, 0, 1]
have lean_s6 : (Or (Not (And (Eq x b) (Eq y b))) (Eq y b)) := @cnfAndPos [(Eq x b), (Eq y b)] 1
have lean_s7 : (Or (Eq y b) (Not (And (Eq x b) (Eq y b)))) := by permutateOr lean_s6, [1, 0]
have lean_s8 : (Iff (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) (And (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) ((Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) -> (Eq x y)))) := sorry
have lean_s9 : (And (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) ((Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) -> (Eq x y))) := eqResolve lean_a0 lean_s8
have lean_s10 : (Or (And (Eq x a) (Eq y a)) (And (Eq x b) (Eq y b))) := by andElim lean_s9, 0
have lean_s11 : (Or (Not (And (Eq x a) (Eq y a))) (Eq x a)) := @cnfAndPos [(Eq x a), (Eq y a)] 0
have lean_s12 : (Or (Eq x a) (Not (And (Eq x a) (Eq y a)))) := by permutateOr lean_s11, [1, 0]
have lean_s13 : (Or (And (Eq x a) (And (Eq x b) (Not (Eq y a)))) (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Not (Not (Eq y a)))))) := cnfAndNeg [(Eq x a), (Eq x b), (Not (Eq y a))]
have lean_s14 : (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Or (Not (Not (Eq y a))) (Not (Eq y b))))) :=
  (scope (fun lean_a4 : (Eq x a) =>
    (scope (fun lean_a5 : (Eq x b) =>
      (scope (fun lean_a6 : (Not (Eq y a)) =>
        let lean_s14 := And.intro lean_a4 lean_a5
        have lean_s15 : (And (Not (Eq y a)) (And (Eq x a) (Eq x b))) := And.intro lean_a6 lean_s14
        have lean_s16 : (Or (Not (Not (Eq y a))) (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Not (Eq y b))))) :=
          (scope (fun lean_a6 : (Not (Eq y a)) =>
            (scope (fun lean_a7 : (Eq x a) =>
              (scope (fun lean_a8 : (Eq x b) =>
                have lean_s16 : (Eq Eq Eq) := rfl
                have lean_s17 : (Eq y y) := rfl
                let lean_s18 := by smtCong lean_s16, lean_s17
                have lean_s19 : (Eq b x) := Eq.symm lean_a8
                have lean_s20 : (Eq a x) := Eq.symm lean_a7
                have lean_s21 : (Eq x a) := Eq.symm lean_s20
                have lean_s22 : (Eq b a) := Eq.trans lean_s19 lean_s21
                have lean_s23 : (Iff (Eq y b) (Eq y a)) := by smtCong lean_s18, lean_s22
                have lean_s24 : (Iff (Eq y a) False) := falseIntro lean_a6
                have lean_s25 : (Iff (Eq y b) False) := Iff.trans lean_s23 lean_s24
                have lean_s26 : (Not (Eq y b)) := falseElim lean_s25
                show (Not (Eq y b)) from lean_s26
          ))))))
        have lean_s17 : ((And (Not (Eq y a)) (And (Eq x a) (Eq x b))) -> (Not (Eq y b))) := by liftOrNToImp lean_s16, 3
        have lean_s18 : (Not (Eq y b)) := modusPonens lean_s15 lean_s17
        show (Not (Eq y b)) from lean_s18
  ))))))
have lean_s15 : ((And (Eq x a) (And (Eq x b) (Not (Eq y a)))) -> (Not (Eq y b))) := by liftOrNToImp lean_s14, 3
have lean_s16 : (Or (Not (And (Eq x a) (And (Eq x b) (Not (Eq y a))))) (Not (Eq y b))) := impliesElim lean_s15
have lean_s17 : (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Or (Not (Not (Eq y a))) (Not (Eq y b))))) := by R1 lean_s13, lean_s16, (And (Eq x a) (And (Eq x b) (Not (Eq y a))))
have lean_s18 : (Eq Or Or) := rfl
have lean_s19 : (Iff (Not (Eq x a)) (Not (Eq x a))) := Iff.rfl
let lean_s20 := by smtCong lean_s18, lean_s19
have lean_s21 : (Iff (Not (Eq x b)) (Not (Eq x b))) := Iff.rfl
let lean_s22 := by smtCong lean_s18, lean_s21
have lean_s23 : (Iff (Iff (Not (Not (Eq y a))) (Eq y a)) (Iff (Eq y a) (Not (Not (Eq y a))))) := sorry
have lean_s24 : (Eq Iff Iff) := rfl
have lean_s25 : (Iff (Eq y a) (Eq y a)) := Iff.rfl
let lean_s26 := by smtCong lean_s24, lean_s25
have lean_s27 : (Iff (Not (Not (Eq y a))) (Eq y a)) := sorry
have lean_s28 : (Iff (Iff (Eq y a) (Not (Not (Eq y a)))) (Iff (Eq y a) (Eq y a))) := by smtCong lean_s26, lean_s27
have lean_s29 : (Iff (Iff (Eq y a) (Eq y a)) True) := by simp
have lean_s30 : (Iff (Iff (Eq y a) (Not (Not (Eq y a)))) True) := Iff.trans lean_s28 lean_s29
have lean_s31 : (Iff (Iff (Not (Not (Eq y a))) (Eq y a)) True) := Iff.trans lean_s23 lean_s30
have lean_s32 : (Iff (Not (Not (Eq y a))) (Eq y a)) := trueElim lean_s31
let lean_s33 := by smtCong lean_s18, lean_s32
have lean_s34 : (Iff (Not (Eq y b)) (Not (Eq y b))) := Iff.rfl
let lean_s35 := by smtCong lean_s33, lean_s34
let lean_s36 := by smtCong lean_s22, lean_s35
have lean_s37 : (Iff (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Or (Not (Not (Eq y a))) (Not (Eq y b))))) (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Or (Eq y a) (Not (Eq y b)))))) := by smtCong lean_s20, lean_s36
have lean_s38 : (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Or (Eq y a) (Not (Eq y b))))) := eqResolve lean_s17 lean_s37
have lean_s39 : (Or (Eq y a) (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Not (Eq y b))))) := by permutateOr lean_s38, [2, 0, 1, 3]
let lean_s40 : (Or (Eq y a) (Or (Not (Eq x a)) (Or (Not (Eq x b)) (Not (And (Eq x b) (Eq y b)))))) := by R2 lean_s39, lean_s7, (Eq y b)

have lean_s41 : (Or (Not (And (Eq x b) (Eq y b))) (Eq x b)) := @cnfAndPos [(Eq x b), (Eq y b)] 0
have lean_s42 : (Or (Eq x b) (Not (And (Eq x b) (Eq y b)))) := by permutateOr lean_s41, [1, 0]
have lean_s43 : (Or (Eq y a) (Or (Not (Eq x a)) (Or (Not (And (Eq x b) (Eq y b))) (Not (And (Eq x b) (Eq y b)))))) := by R2 lean_s40, lean_s42, (Eq x b)
have lean_s44 : (Or (Eq y a) (Or (Not (Eq x a)) (Not (And (Eq x b) (Eq y b))))) := by factor lean_s43
let lean_s45 := by R2 lean_s44, lean_s10, (And (Eq x b) (Eq y b))
have lean_s46 : (Or (Not (And (Eq x a) (Eq y a))) (Eq y a)) := @cnfAndPos [(Eq x a), (Eq y a)] 1
have lean_s47 : (Or (Eq y a) (Not (And (Eq x a) (Eq y a)))) := by permutateOr lean_s46, [1, 0]

-- y = a ∨ ¬ x = a ∨ y = a
have lean_s48 : (Or (Eq y a) (Or (Not (Eq x a)) (Eq y a))) := by R1 lean_s45, lean_s47, (And (Eq x a) (Eq y a))
have lean_s49 : (Or (Eq y a) (Not (Eq x a))) := by factor lean_s48
have lean_s50 : (Or (And (Eq x a) (Eq y a)) (Or (Not (Eq x a)) (Not (Eq y a)))) := cnfAndNeg [(Eq x a), (Eq y a)]
have lean_s51 : (Or (Not (Eq x a)) (Or (Not (Eq y a)) (Eq (f x) (f y)))) :=
  (scope (fun lean_a6 : (Eq x a) =>
    (scope (fun lean_a7 : (Eq y a) =>
      have lean_s51 : (And (Eq y a) (Eq x a)) := And.intro lean_a7 lean_a6
      have lean_s52 : (Or (Not (Eq y a)) (Or (Not (Eq x a)) (Eq (f x) (f y)))) :=
        (scope (fun lean_a7 : (Eq y a) =>
          (scope (fun lean_a8 : (Eq x a) =>
            have lean_s52 : (Eq f f) := rfl
            have lean_s53 : (Eq a x) := Eq.symm lean_a8
            have lean_s54 : (Eq x a) := Eq.symm lean_s53
            have lean_s55 : (Eq a y) := Eq.symm lean_a7
            have lean_s56 : (Eq x y) := Eq.trans lean_s54 lean_s55
            have lean_s57 : (Eq (f x) (f y)) := by smtCong lean_s52, lean_s56
            show (Eq (f x) (f y)) from lean_s57
        ))))
      have lean_s53 : ((And (Eq y a) (Eq x a)) -> (Eq (f x) (f y))) := by liftOrNToImp lean_s52, 2
      have lean_s54 : (Eq (f x) (f y)) := modusPonens lean_s51 lean_s53
      show (Eq (f x) (f y)) from lean_s54
  ))))
have lean_s52 : ((And (Eq x a) (Eq y a)) -> (Eq (f x) (f y))) := by liftOrNToImp lean_s51, 2
have lean_s53 : (Or (Not (And (Eq x a) (Eq y a))) (Eq (f x) (f y))) := impliesElim lean_s52
have lean_s54 : (Or (Not (Eq x a)) (Or (Not (Eq y a)) (Eq (f x) (f y)))) := by R1 lean_s50, lean_s53, (And (Eq x a) (Eq y a))
have lean_s55 : (Or (Eq (f x) (f y)) (Or (Not (Eq x a)) (Not (Eq y a)))) := by permutateOr lean_s54, [2, 0, 1]
let lean_s56 := by R1 lean_s49, lean_s55, (Eq y a)
have lean_s57 : (Or (Not (Eq x a)) (Not (Eq x a))) := by R1 lean_s56, lean_a1, (Eq (f x) (f y))
have lean_s58 : (Not (Eq x a)) := by factor lean_s57
have lean_s59 : (Not (And (Eq x a) (Eq y a))) := by R1 lean_s12, lean_s58, (Eq x a)
have lean_s60 : (And (Eq x b) (Eq y b)) := by R1 lean_s10, lean_s59, (And (Eq x a) (Eq y a))
have lean_s61 : (Eq y b) := by R2 lean_s7, lean_s60, (And (Eq x b) (Eq y b))
let lean_s62 := by R2 lean_s5, lean_s61, (Eq y b)
have lean_s63 : (Eq x b) := by R2 lean_s42, lean_s60, (And (Eq x b) (Eq y b))
let lean_s64 := by R2 lean_s62, lean_s63, (Eq x b)
show False from by R1 lean_s64, lean_a1, (Eq (f x) (f y))
