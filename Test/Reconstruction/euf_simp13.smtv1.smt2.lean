import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {A : Type u} [Nonempty A]
variable {f : (A -> A)}
variable {x : A}
variable {x : A}
variable {f : (A -> A)}

theorem th0 : (Eq (Eq (Not (Not (Eq x (f (f (f (f (f x)))))))) (Eq x (f (f (f (f (f x))))))) (Eq (Eq x (f (f (f (f (f x)))))) (Not (Not (Eq x (f (f (f (f (f x)))))))))) → (Eq (Not (Not (Eq x (f (f (f (f (f x)))))))) (Eq x (f (f (f (f (f x))))))) → (Eq (Eq (Not (Not (Eq x (f x)))) (Eq x (f x))) (Eq (Eq x (f x)) (Not (Not (Eq x (f x)))))) → (Eq (Not (Not (Eq x (f x)))) (Eq x (f x))) → (Eq (Eq (f (f (f x))) x) (Eq x (f (f (f x))))) → (Eq (Eq (Not (Not (Eq x (f (f (f x)))))) (Eq x (f (f (f x))))) (Eq (Eq x (f (f (f x)))) (Not (Not (Eq x (f (f (f x)))))))) → (Eq (Eq (f (f x)) x) (Eq x (f (f x)))) → (Eq (Eq (f x) x) (Eq x (f x))) → (Eq (Not (Not (Eq x (f (f (f x)))))) (Eq x (f (f (f x))))) → (Eq (Eq (f (f (f (f x)))) (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x)))))) → (Eq (Eq (f (f (f (f (f x))))) x) (Eq x (f (f (f (f (f x))))))) → (Eq (Eq (Eq x (f (f (f (f (f x)))))) (Eq x (f (f (f (f (f x))))))) True) → (Eq (Eq (f (f (f (f (f x))))) (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) → (Eq (Or (Or (Or (And (Eq (f (f x)) x) (Eq (f (f (f x))) x)) (And (Eq (f (f x)) x) (Eq (f (f (f (f (f x))))) x))) (And (Eq (f (f (f x))) x) (Eq (f (f (f (f x)))) (f (f (f x)))))) (And (Eq (f (f (f x))) x) (Eq (f (f (f (f (f x))))) (f (f (f x)))))) (Or (And (Eq (f (f (f x))) x) (Eq (f (f (f (f (f x))))) (f (f (f x))))) (Or (And (Eq (f (f (f x))) x) (Eq (f (f (f (f x)))) (f (f (f x))))) (Or (And (Eq (f (f x)) x) (Eq (f (f (f x))) x)) (And (Eq (f (f x)) x) (Eq (f (f (f (f (f x))))) x)))))) → (Eq (Eq (Eq x (f x)) (Eq x (f x))) True) → (Eq (Eq (Eq x (f (f (f x)))) (Eq x (f (f (f x))))) True) → (Not (Implies (Or (Or (Or (And (Eq (f (f x)) x) (Eq (f (f (f x))) x)) (And (Eq (f (f x)) x) (Eq (f (f (f (f (f x))))) x))) (And (Eq (f (f (f x))) x) (Eq (f (f (f (f x)))) (f (f (f x)))))) (And (Eq (f (f (f x))) x) (Eq (f (f (f (f (f x))))) (f (f (f x)))))) (Eq (f x) x))) → False :=
fun lean_r0 : (Eq (Eq (Not (Not (Eq x (f (f (f (f (f x)))))))) (Eq x (f (f (f (f (f x))))))) (Eq (Eq x (f (f (f (f (f x)))))) (Not (Not (Eq x (f (f (f (f (f x)))))))))) =>
fun lean_r1 : (Eq (Not (Not (Eq x (f (f (f (f (f x)))))))) (Eq x (f (f (f (f (f x))))))) =>
fun lean_r2 : (Eq (Eq (Not (Not (Eq x (f x)))) (Eq x (f x))) (Eq (Eq x (f x)) (Not (Not (Eq x (f x)))))) =>
fun lean_r3 : (Eq (Not (Not (Eq x (f x)))) (Eq x (f x))) =>
fun lean_r4 : (Eq (Eq (f (f (f x))) x) (Eq x (f (f (f x))))) =>
fun lean_r5 : (Eq (Eq (Not (Not (Eq x (f (f (f x)))))) (Eq x (f (f (f x))))) (Eq (Eq x (f (f (f x)))) (Not (Not (Eq x (f (f (f x)))))))) =>
fun lean_r6 : (Eq (Eq (f (f x)) x) (Eq x (f (f x)))) =>
fun lean_r7 : (Eq (Eq (f x) x) (Eq x (f x))) =>
fun lean_r8 : (Eq (Not (Not (Eq x (f (f (f x)))))) (Eq x (f (f (f x))))) =>
fun lean_r9 : (Eq (Eq (f (f (f (f x)))) (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x)))))) =>
fun lean_r10 : (Eq (Eq (f (f (f (f (f x))))) x) (Eq x (f (f (f (f (f x))))))) =>
fun lean_r11 : (Eq (Eq (Eq x (f (f (f (f (f x)))))) (Eq x (f (f (f (f (f x))))))) True) =>
fun lean_r12 : (Eq (Eq (f (f (f (f (f x))))) (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) =>
fun lean_r13 : (Eq (Or (Or (Or (And (Eq (f (f x)) x) (Eq (f (f (f x))) x)) (And (Eq (f (f x)) x) (Eq (f (f (f (f (f x))))) x))) (And (Eq (f (f (f x))) x) (Eq (f (f (f (f x)))) (f (f (f x)))))) (And (Eq (f (f (f x))) x) (Eq (f (f (f (f (f x))))) (f (f (f x)))))) (Or (And (Eq (f (f (f x))) x) (Eq (f (f (f (f (f x))))) (f (f (f x))))) (Or (And (Eq (f (f (f x))) x) (Eq (f (f (f (f x)))) (f (f (f x))))) (Or (And (Eq (f (f x)) x) (Eq (f (f (f x))) x)) (And (Eq (f (f x)) x) (Eq (f (f (f (f (f x))))) x)))))) =>
fun lean_r14 : (Eq (Eq (Eq x (f x)) (Eq x (f x))) True) =>
fun lean_r15 : (Eq (Eq (Eq x (f (f (f x)))) (Eq x (f (f (f x))))) True) =>
fun lean_a16 : (Not (Implies (Or (Or (Or (And (Eq (f (f x)) x) (Eq (f (f (f x))) x)) (And (Eq (f (f x)) x) (Eq (f (f (f (f (f x))))) x))) (And (Eq (f (f (f x))) x) (Eq (f (f (f (f x)))) (f (f (f x)))))) (And (Eq (f (f (f x))) x) (Eq (f (f (f (f (f x))))) (f (f (f x)))))) (Eq (f x) x))) => by
have lean_s0 : (Eq Or Or) := rfl
let lean_s1 := flipCongrArg lean_r4 [And]
have lean_s2 : (Eq (And (Eq (f (f (f x))) x) (Eq (f (f (f (f (f x))))) (f (f (f x))))) (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x)))))))) := congr lean_s1 lean_r12
let lean_s3 := congr lean_s0 lean_s2
let lean_s4 := flipCongrArg lean_r4 [And]
have lean_s5 : (Eq (And (Eq (f (f (f x))) x) (Eq (f (f (f (f x)))) (f (f (f x))))) (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x))))))) := congr lean_s4 lean_r9
let lean_s6 := congr lean_s0 lean_s5
let lean_s7 := flipCongrArg lean_r6 [And]
have lean_s8 : (Eq (And (Eq (f (f x)) x) (Eq (f (f (f x))) x)) (And (Eq x (f (f x))) (Eq x (f (f (f x)))))) := congr lean_s7 lean_r4
let lean_s9 := congr lean_s0 lean_s8
let lean_s10 := flipCongrArg lean_r6 [And]
have lean_s11 : (Eq (And (Eq (f (f x)) x) (Eq (f (f (f (f (f x))))) x)) (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x)))))))) := congr lean_s10 lean_r10
let lean_s12 := congr lean_s9 lean_s11
let lean_s13 := congr lean_s6 lean_s12
have lean_s14 : (Eq (Or (And (Eq (f (f (f x))) x) (Eq (f (f (f (f (f x))))) (f (f (f x))))) (Or (And (Eq (f (f (f x))) x) (Eq (f (f (f (f x)))) (f (f (f x))))) (Or (And (Eq (f (f x)) x) (Eq (f (f (f x))) x)) (And (Eq (f (f x)) x) (Eq (f (f (f (f (f x))))) x))))) (Or (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) (Or (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x)))))) (Or (And (Eq x (f (f x))) (Eq x (f (f (f x))))) (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x))))))))))) := congr lean_s3 lean_s13
have lean_s15 : (Eq (Or (Or (Or (And (Eq (f (f x)) x) (Eq (f (f (f x))) x)) (And (Eq (f (f x)) x) (Eq (f (f (f (f (f x))))) x))) (And (Eq (f (f (f x))) x) (Eq (f (f (f (f x)))) (f (f (f x)))))) (And (Eq (f (f (f x))) x) (Eq (f (f (f (f (f x))))) (f (f (f x)))))) (Or (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) (Or (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x)))))) (Or (And (Eq x (f (f x))) (Eq x (f (f (f x))))) (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x))))))))))) := Eq.trans lean_r13 lean_s14
let lean_s16 := flipCongrArg lean_s15 [Implies]
have lean_s17 : (Eq (Implies (Or (Or (Or (And (Eq (f (f x)) x) (Eq (f (f (f x))) x)) (And (Eq (f (f x)) x) (Eq (f (f (f (f (f x))))) x))) (And (Eq (f (f (f x))) x) (Eq (f (f (f (f x)))) (f (f (f x)))))) (And (Eq (f (f (f x))) x) (Eq (f (f (f (f (f x))))) (f (f (f x)))))) (Eq (f x) x)) (Implies (Or (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) (Or (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x)))))) (Or (And (Eq x (f (f x))) (Eq x (f (f (f x))))) (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x)))))))))) (Eq x (f x)))) := congr lean_s16 lean_r7
have lean_s18 : (Eq (Not (Implies (Or (Or (Or (And (Eq (f (f x)) x) (Eq (f (f (f x))) x)) (And (Eq (f (f x)) x) (Eq (f (f (f (f (f x))))) x))) (And (Eq (f (f (f x))) x) (Eq (f (f (f (f x)))) (f (f (f x)))))) (And (Eq (f (f (f x))) x) (Eq (f (f (f (f (f x))))) (f (f (f x)))))) (Eq (f x) x))) (Not (Implies (Or (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) (Or (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x)))))) (Or (And (Eq x (f (f x))) (Eq x (f (f (f x))))) (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x)))))))))) (Eq x (f x))))) := flipCongrArg lean_s17 [Not]
have lean_s19 : (Not (Implies (Or (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) (Or (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x)))))) (Or (And (Eq x (f (f x))) (Eq x (f (f (f x))))) (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x)))))))))) (Eq x (f x)))) := eqResolve lean_a16 lean_s18
have lean_s20 : (Or (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) (Or (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x)))))) (Or (And (Eq x (f (f x))) (Eq x (f (f (f x))))) (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x)))))))))) := notImplies1 lean_s19
have lean_s21 : (Or (Not (And (Eq x (f (f x))) (Eq x (f (f (f x)))))) (Eq x (f (f x)))) := @cnfAndPos [(Eq x (f (f x))), (Eq x (f (f (f x))))] 0
have lean_s22 : (Or (Eq x (f (f x))) (Not (And (Eq x (f (f x))) (Eq x (f (f (f x))))))) := by permutateOr lean_s21, [1, 0], (- 1)
have lean_s23 : (Or (And (Not (Eq x (f (f (f (f (f x))))))) (Eq x (f (f (f x))))) (Or (Not (Not (Eq x (f (f (f (f (f x)))))))) (Not (Eq x (f (f (f x))))))) := cnfAndNeg [(Not (Eq x (f (f (f (f (f x))))))), (Eq x (f (f (f x))))]
have lean_s24 : (Or (Not (Not (Eq x (f (f (f (f (f x)))))))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq x (f (f x)))))) :=
  (scope (fun lean_a17 : (Not (Eq x (f (f (f (f (f x))))))) =>
    (scope (fun lean_a18 : (Eq x (f (f (f x)))) =>
      have lean_s24 : (Eq x x) := rfl
      let lean_s25 := flipCongrArg lean_s24 [Eq]
      have lean_s26 : (Eq (f (f (f x))) x) := Eq.symm lean_a18
      have lean_s27 : (Eq x (f (f (f x)))) := Eq.symm lean_s26
      have lean_s28 : (Eq (f x) (f (f (f (f x))))) := flipCongrArg lean_s27 [f]
      have lean_s29 : (Eq (f (f x)) (f (f (f (f (f x)))))) := flipCongrArg lean_s28 [f]
      have lean_s30 : (Eq (Eq x (f (f x))) (Eq x (f (f (f (f (f x))))))) := congr lean_s25 lean_s29
      have lean_s31 : (Eq (Eq x (f (f (f (f (f x)))))) False) := falseIntro lean_a17
      have lean_s32 : (Eq (Eq x (f (f x))) False) := Eq.trans lean_s30 lean_s31
      have lean_s33 : (Not (Eq x (f (f x)))) := falseElim lean_s32
      show (Not (Eq x (f (f x)))) from lean_s33
  ))))
have lean_s25 : (Implies (And (Not (Eq x (f (f (f (f (f x))))))) (Eq x (f (f (f x))))) (Not (Eq x (f (f x))))) := by liftOrNToImp lean_s24, 2
have lean_s26 : (Or (Not (And (Not (Eq x (f (f (f (f (f x))))))) (Eq x (f (f (f x)))))) (Not (Eq x (f (f x))))) := impliesElim lean_s25
have lean_s27 : (Or (Not (Not (Eq x (f (f (f (f (f x)))))))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq x (f (f x)))))) := by R1 lean_s23, lean_s26, (And (Not (Eq x (f (f (f (f (f x))))))) (Eq x (f (f (f x))))), [(- 1), (- 1)]
have lean_s28 : (Eq Or Or) := rfl
have lean_s29 : (Eq (Eq x (f (f (f (f (f x)))))) (Eq x (f (f (f (f (f x))))))) := rfl
let lean_s30 := flipCongrArg lean_s29 [Eq]
have lean_s31 : (Eq (Eq (Eq x (f (f (f (f (f x)))))) (Not (Not (Eq x (f (f (f (f (f x))))))))) (Eq (Eq x (f (f (f (f (f x)))))) (Eq x (f (f (f (f (f x)))))))) := congr lean_s30 lean_r1
have lean_s32 : (Eq (Eq (Eq x (f (f (f (f (f x)))))) (Not (Not (Eq x (f (f (f (f (f x))))))))) True) := Eq.trans lean_s31 lean_r11
have lean_s33 : (Eq (Eq (Not (Not (Eq x (f (f (f (f (f x)))))))) (Eq x (f (f (f (f (f x))))))) True) := Eq.trans lean_r0 lean_s32
have lean_s34 : (Eq (Not (Not (Eq x (f (f (f (f (f x)))))))) (Eq x (f (f (f (f (f x))))))) := trueElim lean_s33
let lean_s35 := congr lean_s28 lean_s34
have lean_s36 : (Eq (Not (Eq x (f (f (f x))))) (Not (Eq x (f (f (f x)))))) := rfl
let lean_s37 := congr lean_s28 lean_s36
have lean_s38 : (Eq (Not (Eq x (f (f x)))) (Not (Eq x (f (f x))))) := rfl
let lean_s39 := congr lean_s37 lean_s38
have lean_s40 : (Eq (Or (Not (Not (Eq x (f (f (f (f (f x)))))))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq x (f (f x)))))) (Or (Eq x (f (f (f (f (f x)))))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq x (f (f x))))))) := congr lean_s35 lean_s39
have lean_s41 : (Or (Eq x (f (f (f (f (f x)))))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq x (f (f x)))))) := eqResolve lean_s27 lean_s40
have lean_s42 : (Or (And (Eq x (f (f (f x)))) (Eq x (f (f (f (f (f x))))))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq x (f (f (f (f (f x))))))))) := cnfAndNeg [(Eq x (f (f (f x)))), (Eq x (f (f (f (f (f x))))))]
have lean_s43 : (Or (Not (Eq x (f (f (f x))))) (Or (Not (Eq x (f (f (f (f (f x))))))) (Eq (f (f (f x))) (f (f (f (f x))))))) :=
  (scope (fun lean_a19 : (Eq x (f (f (f x)))) =>
    (scope (fun lean_a20 : (Eq x (f (f (f (f (f x)))))) =>
      have lean_s43 : (Eq (f (f (f x))) x) := Eq.symm lean_a19
      have lean_s44 : (Eq x (f (f (f x)))) := Eq.symm lean_s43
      have lean_s45 : (Eq (f x) (f (f (f (f x))))) := flipCongrArg lean_s44 [f]
      have lean_s46 : (Eq (f (f x)) (f (f (f (f (f x)))))) := flipCongrArg lean_s45 [f]
      have lean_s47 : (Eq (f (f (f (f (f x))))) x) := Eq.symm lean_a20
      have lean_s48 : (Eq (f (f x)) x) := Eq.trans lean_s46 lean_s47
      have lean_s49 : (Eq (f (f (f x))) (f x)) := flipCongrArg lean_s48 [f]
      have lean_s50 : (Eq (f (f (f x))) (f (f (f (f x))))) := Eq.trans lean_s49 lean_s45
      show (Eq (f (f (f x))) (f (f (f (f x))))) from lean_s50
  ))))
have lean_s44 : (Implies (And (Eq x (f (f (f x)))) (Eq x (f (f (f (f (f x))))))) (Eq (f (f (f x))) (f (f (f (f x)))))) := by liftOrNToImp lean_s43, 2
have lean_s45 : (Or (Not (And (Eq x (f (f (f x)))) (Eq x (f (f (f (f (f x)))))))) (Eq (f (f (f x))) (f (f (f (f x)))))) := impliesElim lean_s44
have lean_s46 : (Or (Not (Eq x (f (f (f x))))) (Or (Not (Eq x (f (f (f (f (f x))))))) (Eq (f (f (f x))) (f (f (f (f x))))))) := by R1 lean_s42, lean_s45, (And (Eq x (f (f (f x)))) (Eq x (f (f (f (f (f x))))))), [(- 1), (- 1)]
have lean_s47 : (Or (Eq (f (f (f x))) (f (f (f (f x))))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq x (f (f (f (f (f x))))))))) := by permutateOr lean_s46, [2, 0, 1], (- 1)
have lean_s48 : (Or (And (Not (Eq x (f x))) (Eq x (f (f (f x))))) (Or (Not (Not (Eq x (f x)))) (Not (Eq x (f (f (f x))))))) := cnfAndNeg [(Not (Eq x (f x))), (Eq x (f (f (f x))))]
have lean_s49 : (Or (Not (Not (Eq x (f x)))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq (f (f (f x))) (f (f (f (f x)))))))) :=
  (scope (fun lean_a20 : (Not (Eq x (f x))) =>
    (scope (fun lean_a21 : (Eq x (f (f (f x)))) =>
      have lean_s49 : (Eq (f (f (f x))) x) := Eq.symm lean_a21
      have lean_s50 : (Eq x (f (f (f x)))) := Eq.symm lean_s49
      have lean_s51 : (Eq (f (f (f x))) x) := Eq.symm lean_s50
      let lean_s52 := flipCongrArg lean_s51 [Eq]
      have lean_s53 : (Eq (f (f (f (f x)))) (f x)) := flipCongrArg lean_s51 [f]
      have lean_s54 : (Eq (Eq (f (f (f x))) (f (f (f (f x))))) (Eq x (f x))) := congr lean_s52 lean_s53
      have lean_s55 : (Not (Implies (Or (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) (Or (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x)))))) (Or (And (Eq x (f (f x))) (Eq x (f (f (f x))))) (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x)))))))))) (Eq x (f x)))) := eqResolve lean_a16 lean_s18
      have lean_s56 : (Not (Eq x (f x))) := notImplies2 lean_s55
      have lean_s57 : (Eq (Eq x (f x)) False) := falseIntro lean_s56
      have lean_s58 : (Eq (Eq (f (f (f x))) (f (f (f (f x))))) False) := Eq.trans lean_s54 lean_s57
      have lean_s59 : (Not (Eq (f (f (f x))) (f (f (f (f x)))))) := falseElim lean_s58
      show (Not (Eq (f (f (f x))) (f (f (f (f x)))))) from lean_s59
  ))))
have lean_s50 : (Implies (And (Not (Eq x (f x))) (Eq x (f (f (f x))))) (Not (Eq (f (f (f x))) (f (f (f (f x))))))) := by liftOrNToImp lean_s49, 2
have lean_s51 : (Or (Not (And (Not (Eq x (f x))) (Eq x (f (f (f x)))))) (Not (Eq (f (f (f x))) (f (f (f (f x))))))) := impliesElim lean_s50
have lean_s52 : (Or (Not (Not (Eq x (f x)))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq (f (f (f x))) (f (f (f (f x)))))))) := by R1 lean_s48, lean_s51, (And (Not (Eq x (f x))) (Eq x (f (f (f x))))), [(- 1), (- 1)]
have lean_s53 : (Eq Or Or) := rfl
have lean_s54 : (Eq (Eq x (f x)) (Eq x (f x))) := rfl
let lean_s55 := flipCongrArg lean_s54 [Eq]
have lean_s56 : (Eq (Eq (Eq x (f x)) (Not (Not (Eq x (f x))))) (Eq (Eq x (f x)) (Eq x (f x)))) := congr lean_s55 lean_r3
have lean_s57 : (Eq (Eq (Eq x (f x)) (Not (Not (Eq x (f x))))) True) := Eq.trans lean_s56 lean_r14
have lean_s58 : (Eq (Eq (Not (Not (Eq x (f x)))) (Eq x (f x))) True) := Eq.trans lean_r2 lean_s57
have lean_s59 : (Eq (Not (Not (Eq x (f x)))) (Eq x (f x))) := trueElim lean_s58
let lean_s60 := congr lean_s53 lean_s59
let lean_s61 := congr lean_s53 lean_s36
have lean_s62 : (Eq (Not (Eq (f (f (f x))) (f (f (f (f x)))))) (Not (Eq (f (f (f x))) (f (f (f (f x))))))) := rfl
let lean_s63 := congr lean_s61 lean_s62
have lean_s64 : (Eq (Or (Not (Not (Eq x (f x)))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq (f (f (f x))) (f (f (f (f x)))))))) (Or (Eq x (f x)) (Or (Not (Eq x (f (f (f x))))) (Not (Eq (f (f (f x))) (f (f (f (f x))))))))) := congr lean_s60 lean_s63
have lean_s65 : (Or (Eq x (f x)) (Or (Not (Eq x (f (f (f x))))) (Not (Eq (f (f (f x))) (f (f (f (f x)))))))) := eqResolve lean_s52 lean_s64
have lean_s66 : (Not (Eq x (f x))) := notImplies2 lean_s19
let lean_s67 := by R1 lean_s65, lean_s66, (Eq x (f x)), [(- 1), 0]
have lean_s68 : (Or (And (Not (Eq x (f (f (f x))))) (Eq x (f (f x)))) (Or (Not (Not (Eq x (f (f (f x)))))) (Not (Eq x (f (f x)))))) := cnfAndNeg [(Not (Eq x (f (f (f x))))), (Eq x (f (f x)))]
have lean_s69 : (Or (Not (Not (Eq x (f (f (f x)))))) (Or (Not (Eq x (f (f x)))) (Not (Eq x (f (f (f (f (f x))))))))) :=
  (scope (fun lean_a21 : (Not (Eq x (f (f (f x))))) =>
    (scope (fun lean_a22 : (Eq x (f (f x))) =>
      have lean_s69 : (Eq x x) := rfl
      let lean_s70 := flipCongrArg lean_s69 [Eq]
      have lean_s71 : (Eq (f (f x)) x) := Eq.symm lean_a22
      have lean_s72 : (Eq x (f (f x))) := Eq.symm lean_s71
      have lean_s73 : (Eq (f x) (f (f (f x)))) := flipCongrArg lean_s72 [f]
      have lean_s74 : (Eq (f (f (f x))) (f x)) := Eq.symm lean_s73
      have lean_s75 : (Eq (f (f (f (f x)))) (f (f x))) := flipCongrArg lean_s74 [f]
      have lean_s76 : (Eq (f (f (f (f x)))) x) := Eq.trans lean_s75 lean_s71
      have lean_s77 : (Eq (f (f (f (f (f x))))) (f x)) := flipCongrArg lean_s76 [f]
      have lean_s78 : (Eq (f (f (f (f (f x))))) (f (f (f x)))) := Eq.trans lean_s77 lean_s73
      have lean_s79 : (Eq (Eq x (f (f (f (f (f x)))))) (Eq x (f (f (f x))))) := congr lean_s70 lean_s78
      have lean_s80 : (Eq (Eq x (f (f (f x)))) False) := falseIntro lean_a21
      have lean_s81 : (Eq (Eq x (f (f (f (f (f x)))))) False) := Eq.trans lean_s79 lean_s80
      have lean_s82 : (Not (Eq x (f (f (f (f (f x))))))) := falseElim lean_s81
      show (Not (Eq x (f (f (f (f (f x))))))) from lean_s82
  ))))
have lean_s70 : (Implies (And (Not (Eq x (f (f (f x))))) (Eq x (f (f x)))) (Not (Eq x (f (f (f (f (f x)))))))) := by liftOrNToImp lean_s69, 2
have lean_s71 : (Or (Not (And (Not (Eq x (f (f (f x))))) (Eq x (f (f x))))) (Not (Eq x (f (f (f (f (f x)))))))) := impliesElim lean_s70
have lean_s72 : (Or (Not (Not (Eq x (f (f (f x)))))) (Or (Not (Eq x (f (f x)))) (Not (Eq x (f (f (f (f (f x))))))))) := by R1 lean_s68, lean_s71, (And (Not (Eq x (f (f (f x))))) (Eq x (f (f x)))), [(- 1), (- 1)]
have lean_s73 : (Eq Or Or) := rfl
have lean_s74 : (Eq (Eq x (f (f (f x)))) (Eq x (f (f (f x))))) := rfl
let lean_s75 := flipCongrArg lean_s74 [Eq]
have lean_s76 : (Eq (Eq (Eq x (f (f (f x)))) (Not (Not (Eq x (f (f (f x))))))) (Eq (Eq x (f (f (f x)))) (Eq x (f (f (f x)))))) := congr lean_s75 lean_r8
have lean_s77 : (Eq (Eq (Eq x (f (f (f x)))) (Not (Not (Eq x (f (f (f x))))))) True) := Eq.trans lean_s76 lean_r15
have lean_s78 : (Eq (Eq (Not (Not (Eq x (f (f (f x)))))) (Eq x (f (f (f x))))) True) := Eq.trans lean_r5 lean_s77
have lean_s79 : (Eq (Not (Not (Eq x (f (f (f x)))))) (Eq x (f (f (f x))))) := trueElim lean_s78
let lean_s80 := congr lean_s73 lean_s79
let lean_s81 := congr lean_s73 lean_s38
have lean_s82 : (Eq (Not (Eq x (f (f (f (f (f x))))))) (Not (Eq x (f (f (f (f (f x)))))))) := rfl
let lean_s83 := congr lean_s81 lean_s82
have lean_s84 : (Eq (Or (Not (Not (Eq x (f (f (f x)))))) (Or (Not (Eq x (f (f x)))) (Not (Eq x (f (f (f (f (f x))))))))) (Or (Eq x (f (f (f x)))) (Or (Not (Eq x (f (f x)))) (Not (Eq x (f (f (f (f (f x)))))))))) := congr lean_s80 lean_s83
have lean_s85 : (Or (Eq x (f (f (f x)))) (Or (Not (Eq x (f (f x)))) (Not (Eq x (f (f (f (f (f x))))))))) := eqResolve lean_s72 lean_s84
have lean_s86 : (Or (Not (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x)))))))) (Eq x (f (f (f (f (f x))))))) := @cnfAndPos [(Eq x (f (f x))), (Eq x (f (f (f (f (f x))))))] 1
have lean_s87 : (Or (Eq x (f (f (f (f (f x)))))) (Not (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x))))))))) := by permutateOr lean_s86, [1, 0], (- 1)
let lean_s88 := by R2 lean_s85, lean_s87, (Eq x (f (f (f (f (f x)))))), [(- 1), (- 1)]
have lean_s89 : (Or (Not (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x)))))))) (Eq x (f (f x)))) := @cnfAndPos [(Eq x (f (f x))), (Eq x (f (f (f (f (f x))))))] 0
have lean_s90 : (Or (Eq x (f (f x))) (Not (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x))))))))) := by permutateOr lean_s89, [1, 0], (- 1)
have lean_s91 : (Or (Eq x (f (f (f x)))) (Or (Not (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x)))))))) (Not (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x)))))))))) := by R2 lean_s88, lean_s90, (Eq x (f (f x))), [(- 1), (- 1)]
have lean_s92 : (Or (Eq x (f (f (f x)))) (Not (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x))))))))) := by factor lean_s91, (- 1)
let lean_s93 := by R2 lean_s92, lean_s20, (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x))))))), [(- 1), (- 1)]
have lean_s94 : (Or (Not (And (Eq x (f (f x))) (Eq x (f (f (f x)))))) (Eq x (f (f (f x))))) := @cnfAndPos [(Eq x (f (f x))), (Eq x (f (f (f x))))] 1
have lean_s95 : (Or (Eq x (f (f (f x)))) (Not (And (Eq x (f (f x))) (Eq x (f (f (f x))))))) := by permutateOr lean_s94, [1, 0], (- 1)
let lean_s96 := by R1 lean_s93, lean_s95, (And (Eq x (f (f x))) (Eq x (f (f (f x))))), [(- 1), (- 1)]
have lean_s97 : (Or (Not (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x))))))) (Eq x (f (f (f x))))) := @cnfAndPos [(Eq x (f (f (f x)))), (Eq (f (f (f x))) (f (f (f (f x)))))] 0
have lean_s98 : (Or (Eq x (f (f (f x)))) (Not (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x)))))))) := by permutateOr lean_s97, [1, 0], (- 1)
let lean_s99 := by R1 lean_s96, lean_s98, (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x)))))), [(- 1), (- 1)]
have lean_s100 : (Or (Not (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x)))))))) (Eq x (f (f (f x))))) := @cnfAndPos [(Eq x (f (f (f x)))), (Eq (f (f (f x))) (f (f (f (f (f x))))))] 0
have lean_s101 : (Or (Eq x (f (f (f x)))) (Not (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))))) := by permutateOr lean_s100, [1, 0], (- 1)
have lean_s102 : (Or (Eq x (f (f (f x)))) (Or (Eq x (f (f (f x)))) (Or (Eq x (f (f (f x)))) (Eq x (f (f (f x))))))) := by R1 lean_s99, lean_s101, (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))), [(- 1), (- 1)]
have lean_s103 : (Eq x (f (f (f x)))) := by factor lean_s102, 3
have lean_s104 : (Not (Eq (f (f (f x))) (f (f (f (f x)))))) := by R2 lean_s67, lean_s103, (Eq x (f (f (f x)))), [(- 1), 0]
let lean_s105 := by R1 lean_s47, lean_s104, (Eq (f (f (f x))) (f (f (f (f x))))), [(- 1), 0]
have lean_s106 : (Not (Eq x (f (f (f (f (f x))))))) := by R2 lean_s105, lean_s103, (Eq x (f (f (f x)))), [(- 1), 0]
let lean_s107 := by R1 lean_s41, lean_s106, (Eq x (f (f (f (f (f x)))))), [(- 1), 0]
have lean_s108 : (Not (Eq x (f (f x)))) := by R2 lean_s107, lean_s103, (Eq x (f (f (f x)))), [(- 1), 0]
have lean_s109 : (Not (And (Eq x (f (f x))) (Eq x (f (f (f x)))))) := by R1 lean_s22, lean_s108, (Eq x (f (f x))), [(- 1), 0]
let lean_s110 := by R1 lean_s20, lean_s109, (And (Eq x (f (f x))) (Eq x (f (f (f x))))), [(- 1), 0]
have lean_s111 : (Or (Not (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x)))))))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) := @cnfAndPos [(Eq x (f (f (f x)))), (Eq (f (f (f x))) (f (f (f (f (f x))))))] 1
have lean_s112 : (Or (Eq (f (f (f x))) (f (f (f (f (f x)))))) (Not (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))))) := by permutateOr lean_s111, [1, 0], (- 1)
have lean_s113 : (Or (Not (Not (Eq x (f (f (f (f (f x)))))))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq (f (f (f x))) (f (f (f (f (f x))))))))) :=
  (scope (fun lean_a23 : (Not (Eq x (f (f (f (f (f x))))))) =>
    (scope (fun lean_a24 : (Eq x (f (f (f x)))) =>
      have lean_s113 : (Eq (f (f (f x))) x) := Eq.symm lean_a24
      have lean_s114 : (Eq x (f (f (f x)))) := Eq.symm lean_s113
      have lean_s115 : (Eq (f (f (f x))) x) := Eq.symm lean_s114
      let lean_s116 := flipCongrArg lean_s115 [Eq]
      have lean_s117 : (Eq (f (f (f (f (f x))))) (f (f (f (f (f x)))))) := rfl
      have lean_s118 : (Eq (Eq (f (f (f x))) (f (f (f (f (f x)))))) (Eq x (f (f (f (f (f x))))))) := congr lean_s116 lean_s117
      have lean_s119 : (Eq (Eq x (f (f (f (f (f x)))))) False) := falseIntro lean_a23
      have lean_s120 : (Eq (Eq (f (f (f x))) (f (f (f (f (f x)))))) False) := Eq.trans lean_s118 lean_s119
      have lean_s121 : (Not (Eq (f (f (f x))) (f (f (f (f (f x))))))) := falseElim lean_s120
      show (Not (Eq (f (f (f x))) (f (f (f (f (f x))))))) from lean_s121
  ))))
have lean_s114 : (Implies (And (Not (Eq x (f (f (f (f (f x))))))) (Eq x (f (f (f x))))) (Not (Eq (f (f (f x))) (f (f (f (f (f x)))))))) := by liftOrNToImp lean_s113, 2
have lean_s115 : (Or (Not (And (Not (Eq x (f (f (f (f (f x))))))) (Eq x (f (f (f x)))))) (Not (Eq (f (f (f x))) (f (f (f (f (f x)))))))) := impliesElim lean_s114
have lean_s116 : (Or (Not (Not (Eq x (f (f (f (f (f x)))))))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq (f (f (f x))) (f (f (f (f (f x))))))))) := by R1 lean_s23, lean_s115, (And (Not (Eq x (f (f (f (f (f x))))))) (Eq x (f (f (f x))))), [(- 1), (- 1)]
have lean_s117 : (Eq Or Or) := rfl
let lean_s118 := congr lean_s117 lean_s34
let lean_s119 := congr lean_s117 lean_s36
have lean_s120 : (Eq (Not (Eq (f (f (f x))) (f (f (f (f (f x))))))) (Not (Eq (f (f (f x))) (f (f (f (f (f x)))))))) := rfl
let lean_s121 := congr lean_s119 lean_s120
have lean_s122 : (Eq (Or (Not (Not (Eq x (f (f (f (f (f x)))))))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq (f (f (f x))) (f (f (f (f (f x))))))))) (Or (Eq x (f (f (f (f (f x)))))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq (f (f (f x))) (f (f (f (f (f x)))))))))) := congr lean_s118 lean_s121
have lean_s123 : (Or (Eq x (f (f (f (f (f x)))))) (Or (Not (Eq x (f (f (f x))))) (Not (Eq (f (f (f x))) (f (f (f (f (f x))))))))) := eqResolve lean_s116 lean_s122
let lean_s124 := by R1 lean_s123, lean_s106, (Eq x (f (f (f (f (f x)))))), [(- 1), 0]
have lean_s125 : (Not (Eq (f (f (f x))) (f (f (f (f (f x))))))) := by R2 lean_s124, lean_s103, (Eq x (f (f (f x)))), [(- 1), 0]
have lean_s126 : (Not (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x)))))))) := by R1 lean_s112, lean_s125, (Eq (f (f (f x))) (f (f (f (f (f x)))))), [(- 1), 0]
let lean_s127 := by R1 lean_s110, lean_s126, (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))), [(- 1), 0]
have lean_s128 : (Or (Not (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x))))))) (Eq (f (f (f x))) (f (f (f (f x)))))) := @cnfAndPos [(Eq x (f (f (f x)))), (Eq (f (f (f x))) (f (f (f (f x)))))] 1
have lean_s129 : (Or (Eq (f (f (f x))) (f (f (f (f x))))) (Not (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x)))))))) := by permutateOr lean_s128, [1, 0], (- 1)
have lean_s130 : (Not (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x))))))) := by R1 lean_s129, lean_s104, (Eq (f (f (f x))) (f (f (f (f x))))), [(- 1), 0]
let lean_s131 := by R1 lean_s127, lean_s130, (And (Eq x (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f x)))))), [(- 1), 0]
have lean_s132 : (Not (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x)))))))) := by R1 lean_s87, lean_s106, (Eq x (f (f (f (f (f x)))))), [(- 1), 0]
exact (show False from by R1 lean_s131, lean_s132, (And (Eq x (f (f x))) (Eq x (f (f (f (f (f x))))))), [0, 0])
