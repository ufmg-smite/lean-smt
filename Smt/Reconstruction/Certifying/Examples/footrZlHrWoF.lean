-- import Smt.Reconstruction.Certifying
open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000

variable {f : (Prop -> Prop)}
variable {f : (Prop -> Prop)}

theorem th0 : (Eq (Eq True False) False) → (Eq (Eq (Not (Not (f True))) (f True)) (Eq (f True) (Not (Not (f True))))) → (Eq (Eq (Not (Not (Or (f True) (f False)))) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Not (Not (Or (f True) (f False)))))) → (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) True) → (Eq (Not (Not (f True))) (f True)) → (Eq (Eq True True) True) → (Eq (Eq (f True) (f True)) True) → (Eq (ite (f True) True (f False)) (Or (f True) (f False))) → (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Or (f True) (f False)))) → (Eq (Not False) True) → (Eq (Eq False False) (Not False)) → (Eq (Not (Not False)) False) → (Eq (Eq False False) (Not False)) → (Eq (Not (Not (Or (f True) (f False)))) (Or (f True) (f False))) → (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Or (f True) (f False)))) → (Eq (Eq False False) True) → (Eq (Eq (Not (Not False)) False) (Eq False (Not (Not False)))) → (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) True) → (Not (f True)) → (f (ite (f True) True (f False))) → False :=
fun lean_r0 : (Eq (Eq True False) False) => -- THEORY_REWRITE_BOOL
fun lean_r1 : (Eq (Eq (Not (Not (f True))) (f True)) (Eq (f True) (Not (Not (f True))))) => -- THEORY_REWRITE_BOOL
fun lean_r2 : (Eq (Eq (Not (Not (Or (f True) (f False)))) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Not (Not (Or (f True) (f False)))))) => -- THEORY_REWRITE_BOOL
fun lean_r3 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) True) => -- THEORY_REWRITE_BOOL
fun lean_r4 : (Eq (Not (Not (f True))) (f True)) => -- THEORY_REWRITE_BOOL
fun lean_r5 : (Eq (Eq True True) True) => -- THEORY_REWRITE_BOOL
fun lean_r6 : (Eq (Eq (f True) (f True)) True) => -- THEORY_REWRITE_BOOL
fun lean_r7 : (Eq (ite (f True) True (f False)) (Or (f True) (f False))) => -- THEORY_REWRITE_BOOL
fun lean_r8 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Or (f True) (f False)))) => -- THEORY_REWRITE_BOOL
fun lean_r9 : (Eq (Not False) True) => -- THEORY_REWRITE_BOOL
fun lean_r10 : (Eq (Eq False False) (Not False)) => -- THEORY_REWRITE_BOOL
fun lean_r11 : (Eq (Not (Not False)) False) => -- THEORY_REWRITE_BOOL
fun lean_r12 : (Eq (Eq False False) (Not False)) => -- THEORY_REWRITE_BOOL
fun lean_r13 : (Eq (Not (Not (Or (f True) (f False)))) (Or (f True) (f False))) => -- THEORY_REWRITE_BOOL
fun lean_r14 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Or (f True) (f False)))) => -- THEORY_REWRITE_BOOL
fun lean_r15 : (Eq (Eq False False) True) => -- THEORY_REWRITE_BOOL
fun lean_r16 : (Eq (Eq (Not (Not False)) False) (Eq False (Not (Not False)))) => -- THEORY_REWRITE_BOOL
fun lean_r17 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) True) => -- THEORY_REWRITE_BOOL
fun lean_a18 : (Not (f True)) =>
fun lean_a19 : (f (ite (f True) True (f False))) => by
have lean_s0 : (Or (Not (Not (f True))) (Or (Not True) (Or (Not (Or (f True) (f False))) (Or (Not (f (Or (f True) (f False)))) False)))) :=
  (scope (fun lean_a17 : (Not (f True)) =>
    (scope (fun lean_a18 : True =>
      (scope (fun lean_a19 : (Or (f True) (f False)) =>
        (scope (fun lean_a20 : (f (Or (f True) (f False))) =>
          have lean_s0 : (Eq (f (ite (f True) True (f False))) (f (Or (f True) (f False)))) := flipCongrArg lean_r7 [f]
          have lean_s1 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Or (f True) (f False)))) := rfl
          have lean_s2 : (Eq (Or (f True) (f False)) (Or (f True) (f False))) := rfl
          let lean_s3 := flipCongrArg lean_s2 [Eq]
          have lean_s4 : (Eq (Or (f True) (f False)) (Or (f True) (f False))) := rfl
          have lean_s5 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Or (f True) (f False)))) := congr lean_s3 lean_s4
          let lean_s6 := Eq.trans lean_s1 lean_s5
          have lean_s7 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) True) := Eq.trans lean_s6 lean_r17
          have lean_s8 : (Eq (Or (f True) (f False)) (Or (f True) (f False))) := trueElim lean_s7
          have lean_s9 : (Eq (f (Or (f True) (f False))) (f (Or (f True) (f False)))) := flipCongrArg lean_s8 [f]
          have lean_s10 : (Eq (f (ite (f True) True (f False))) (f (Or (f True) (f False)))) := Eq.trans lean_s0 lean_s9
          have lean_s11 : (f (Or (f True) (f False))) := eqResolve lean_a19 lean_s10
          have lean_s12 : (Eq (f (Or (f True) (f False))) True) := trueIntro lean_s11
          have lean_s13 : (Eq True (f (Or (f True) (f False)))) := Eq.symm lean_s12
          have lean_s14 : (Eq (Or (f True) (f False)) True) := trueIntro lean_a19
          have lean_s15 : (Eq True True) := rfl
          have lean_s16 : (Eq True True) := Eq.symm lean_s15
          have lean_s17 : (Eq (Or (f True) (f False)) True) := Eq.trans lean_s14 lean_s16
          have lean_s18 : (Eq (f (Or (f True) (f False))) (f True)) := flipCongrArg lean_s17 [f]
          let lean_s19 := Eq.trans lean_s13 lean_s18
          have lean_s20 : (Eq True True) := Eq.symm lean_s15
          have lean_s21 : (Eq (f True) (f True)) := flipCongrArg lean_s20 [f]
          have lean_s22 : (Eq (Not (f True)) (Not (f True))) := flipCongrArg lean_s21 [Not]
          have lean_s23 : (Not (f True)) := eqResolve lean_r17 lean_s22
          have lean_s24 : (Eq (f True) False) := falseIntro lean_s23
          have lean_s25 : (Eq True False) := Eq.trans lean_s19 lean_s24
          show False from eqResolve lean_s25 lean_r0
  ))))))))
have lean_s1 : (Not (And (Not (f True)) (And True (And (Or (f True) (f False)) (f (Or (f True) (f False))))))) := by liftOrNToNeg lean_s0
have lean_s2 : (Or (Not (Not (f True))) (Or (Not True) (Or (Not (Or (f True) (f False))) (Not (f (Or (f True) (f False))))))) := flipNotAnd lean_s1 [(Not (f True)), True, (Or (f True) (f False)), (f (Or (f True) (f False)))]
have lean_s3 : (Eq Or Or) := rfl
have lean_s4 : (Eq (f True) (f True)) := rfl
let lean_s5 := flipCongrArg lean_s4 [Eq]
have lean_s6 : (Eq (Eq (f True) (Not (Not (f True)))) (Eq (f True) (f True))) := congr lean_s5 lean_r4
have lean_s7 : (Eq (Eq (f True) (Not (Not (f True)))) True) := Eq.trans lean_s6 lean_r6
have lean_s8 : (Eq (Eq (Not (Not (f True))) (f True)) True) := Eq.trans lean_r1 lean_s7
have lean_s9 : (Eq (Not (Not (f True))) (f True)) := trueElim lean_s8
let lean_s10 := congr lean_s3 lean_s9
have lean_s11 : (Eq (Not True) (Not True)) := rfl
let lean_s12 := congr lean_s3 lean_s11
have lean_s13 : (Eq (Not (Or (f True) (f False))) (Not (Or (f True) (f False)))) := rfl
let lean_s14 := congr lean_s3 lean_s13
have lean_s15 : (Eq (Not (f (Or (f True) (f False)))) (Not (f (Or (f True) (f False))))) := rfl
let lean_s16 := congr lean_s14 lean_s15
let lean_s17 := congr lean_s12 lean_s16
have lean_s18 : (Eq (Or (Not (Not (f True))) (Or (Not True) (Or (Not (Or (f True) (f False))) (Not (f (Or (f True) (f False))))))) (Or (f True) (Or (Not True) (Or (Not (Or (f True) (f False))) (Not (f (Or (f True) (f False)))))))) := congr lean_s10 lean_s17
have lean_s19 : (Or (f True) (Or (Not True) (Or (Not (Or (f True) (f False))) (Not (f (Or (f True) (f False))))))) := eqResolve lean_s2 lean_s18
have lean_s20 : (Or (f True) (Or (Not (f (Or (f True) (f False)))) (Or (Not True) (Not (Or (f True) (f False)))))) := by permutateOr lean_s19, [0, 3, 1, 2], (- 1)
have lean_s21 : (Or (And (f (Or (f True) (f False))) (And (Not (Or (f True) (f False))) (Not False))) (Or (Not (f (Or (f True) (f False)))) (Or (Not (Not (Or (f True) (f False)))) (Not (Not False))))) := cnfAndNeg [(f (Or (f True) (f False))), (Not (Or (f True) (f False))), (Not False)]
have lean_s22 : (Or (Not (f (Or (f True) (f False)))) (Or (Not (Not (Or (f True) (f False)))) (Or (Not (Not False)) (f False)))) :=
  (scope (fun lean_a20 : (f (Or (f True) (f False))) =>
    (scope (fun lean_a21 : (Not (Or (f True) (f False))) =>
      (scope (fun lean_a22 : (Not False) =>
        have lean_s22 : (Eq False False) := rfl
        have lean_s23 : (Eq (Or (f True) (f False)) False) := falseIntro lean_a21
        have lean_s24 : (Eq False (Or (f True) (f False))) := Eq.symm lean_s23
        have lean_s25 : (Eq False (Or (f True) (f False))) := Eq.trans lean_s22 lean_s24
        have lean_s26 : (Eq (f False) (f (Or (f True) (f False)))) := flipCongrArg lean_s25 [f]
        have lean_s27 : (Eq (f (ite (f True) True (f False))) (f (Or (f True) (f False)))) := flipCongrArg lean_r7 [f]
        have lean_s28 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Or (f True) (f False)))) := rfl
        have lean_s29 : (Eq (Or (f True) (f False)) (Or (f True) (f False))) := rfl
        let lean_s30 := flipCongrArg lean_s29 [Eq]
        have lean_s31 : (Eq (Or (f True) (f False)) (Or (f True) (f False))) := rfl
        have lean_s32 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Or (f True) (f False)))) := congr lean_s30 lean_s31
        let lean_s33 := Eq.trans lean_s28 lean_s32
        have lean_s34 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) True) := Eq.trans lean_s33 lean_r17
        have lean_s35 : (Eq (Or (f True) (f False)) (Or (f True) (f False))) := trueElim lean_s34
        have lean_s36 : (Eq (f (Or (f True) (f False))) (f (Or (f True) (f False)))) := flipCongrArg lean_s35 [f]
        have lean_s37 : (Eq (f (ite (f True) True (f False))) (f (Or (f True) (f False)))) := Eq.trans lean_s27 lean_s36
        have lean_s38 : (f (Or (f True) (f False))) := eqResolve lean_a19 lean_s37
        have lean_s39 : (Eq (f (Or (f True) (f False))) True) := trueIntro lean_s38
        have lean_s40 : (Eq (f False) True) := Eq.trans lean_s26 lean_s39
        have lean_s41 : (f False) := trueElim lean_s40
        show (f False) from lean_s41
  ))))))
have lean_s23 : (Implies (And (f (Or (f True) (f False))) (And (Not (Or (f True) (f False))) (Not False))) (f False)) := by liftOrNToImp lean_s22, 3
have lean_s24 : (Or (Not (And (f (Or (f True) (f False))) (And (Not (Or (f True) (f False))) (Not False)))) (f False)) := impliesElim lean_s23
have lean_s25 : (Or (Not (f (Or (f True) (f False)))) (Or (Not (Not (Or (f True) (f False)))) (Or (Not (Not False)) (f False)))) := by R1 lean_s21, lean_s24, (And (f (Or (f True) (f False))) (And (Not (Or (f True) (f False))) (Not False))), [(- 1), (- 1)]
have lean_s26 : (Eq Or Or) := rfl
let lean_s27 := congr lean_s26 lean_s15
have lean_s28 : (Eq (Or (f True) (f False)) (Or (f True) (f False))) := rfl
let lean_s29 := flipCongrArg lean_s28 [Eq]
have lean_s30 : (Eq (Eq (Or (f True) (f False)) (Not (Not (Or (f True) (f False))))) (Eq (Or (f True) (f False)) (Or (f True) (f False)))) := congr lean_s29 lean_r13
have lean_s31 : (Eq (Eq (Or (f True) (f False)) (Not (Not (Or (f True) (f False))))) True) := Eq.trans lean_s30 lean_r17
have lean_s32 : (Eq (Eq (Not (Not (Or (f True) (f False)))) (Or (f True) (f False))) True) := Eq.trans lean_r2 lean_s31
have lean_s33 : (Eq (Not (Not (Or (f True) (f False)))) (Or (f True) (f False))) := trueElim lean_s32
let lean_s34 := congr lean_s26 lean_s33
have lean_s35 : (Eq False False) := rfl
let lean_s36 := flipCongrArg lean_s35 [Eq]
have lean_s37 : (Eq (Eq False (Not (Not False))) (Eq False False)) := congr lean_s36 lean_r11
have lean_s38 : (Eq (Eq False (Not (Not False))) True) := Eq.trans lean_s37 lean_r15
have lean_s39 : (Eq (Eq (Not (Not False)) False) True) := Eq.trans lean_r16 lean_s38
have lean_s40 : (Eq (Not (Not False)) False) := trueElim lean_s39
let lean_s41 := congr lean_s26 lean_s40
have lean_s42 : (Eq (f False) (f False)) := rfl
let lean_s43 := congr lean_s41 lean_s42
let lean_s44 := congr lean_s34 lean_s43
have lean_s45 : (Eq (Or (Not (f (Or (f True) (f False)))) (Or (Not (Not (Or (f True) (f False)))) (Or (Not (Not False)) (f False)))) (Or (Not (f (Or (f True) (f False)))) (Or (Or (f True) (f False)) (Or False (f False))))) := congr lean_s27 lean_s44
have lean_s46 : (Or (Not (f (Or (f True) (f False)))) (Or (Or (f True) (f False)) (Or False (f False)))) := eqResolve lean_s25 lean_s45
have lean_s47 : (Or (Or (f True) (f False)) (Or False (Or (f False) (Not (f (Or (f True) (f False))))))) := by permutateOr lean_s46, [1, 2, 3, 0], (- 1)
have lean_s48 : (Eq False False) := rfl
have lean_s49 : (Not False) := eqResolve lean_s48 lean_r12
let lean_s50 := by R1 lean_s47, lean_s49, False, [(- 1), 0]
have lean_s51 : (Eq (f (ite (f True) True (f False))) (f (Or (f True) (f False)))) := flipCongrArg lean_r7 [f]
have lean_s52 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Or (f True) (f False)))) := rfl
have lean_s53 : (Eq (Or (f True) (f False)) (Or (f True) (f False))) := rfl
let lean_s54 := flipCongrArg lean_s53 [Eq]
have lean_s55 : (Eq (Or (f True) (f False)) (Or (f True) (f False))) := rfl
have lean_s56 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Or (f True) (f False)))) := congr lean_s54 lean_s55
let lean_s57 := Eq.trans lean_s52 lean_s56
have lean_s58 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) True) := Eq.trans lean_s57 lean_r17
have lean_s59 : (Eq (Or (f True) (f False)) (Or (f True) (f False))) := trueElim lean_s58
have lean_s60 : (Eq (f (Or (f True) (f False))) (f (Or (f True) (f False)))) := flipCongrArg lean_s59 [f]
have lean_s61 : (Eq (f (ite (f True) True (f False))) (f (Or (f True) (f False)))) := Eq.trans lean_s51 lean_s60
have lean_s62 : (f (Or (f True) (f False))) := eqResolve lean_a19 lean_s61
let lean_s63 := by R2 lean_s50, lean_s62, (f (Or (f True) (f False))), [(- 1), 0]
have lean_s64 : (Or (Or (f True) (f False)) (Not (f False))) := @cnfOrNeg [(f True), (f False)] 1
let lean_s65 := by R1 lean_s63, lean_s64, (f False), [(- 1), (- 1)]
have lean_s66 : (Eq (Or (f True) (f False)) (Or (f True) (f False))) := rfl
have lean_s67 : (Eq True True) := rfl
have lean_s68 : (Eq True True) := Eq.symm lean_s67
have lean_s69 : (Eq (f True) (f True)) := flipCongrArg lean_s68 [f]
let lean_s70 := flipCongrArg lean_s69 [Or]
have lean_s71 : (Eq False False) := rfl
have lean_s72 : (Eq (Not False) (Not False)) := flipCongrArg lean_s71 [Not]
let lean_s73 := Eq.trans lean_r12 lean_s72
have lean_s74 : (Eq (Eq False False) True) := Eq.trans lean_s73 lean_r9
have lean_s75 : (Eq False False) := trueElim lean_s74
have lean_s76 : (Eq (f False) (f False)) := flipCongrArg lean_s75 [f]
have lean_s77 : (Eq (Or (f True) (f False)) (Or (f True) (f False))) := congr lean_s70 lean_s76
let lean_s78 := flipCongrArg lean_s77 [Eq]
have lean_s79 : (Eq (Or (f True) (f False)) (Or (f True) (f False))) := rfl
have lean_s80 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Or (f True) (f False)))) := congr lean_s78 lean_s79
have lean_s81 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Or (f True) (f False)))) := Eq.trans lean_s80 lean_r14
have lean_s82 : (Eq (Eq (Or (f True) (f False)) (Or (f True) (f False))) (Eq (Or (f True) (f False)) (Or (f True) (f False)))) := Eq.trans lean_r14 lean_s81
have lean_s83 : (Eq (Or (f True) (f False)) (Or (f True) (f False))) := eqResolve lean_s66 lean_s82
have lean_s84 : (Or (Or (f True) (f False)) (Not (Or (f True) (f False)))) := equivElim2 lean_s83
have lean_s85 : (Or (Or (f True) (f False)) (Or (f True) (f False))) := by R1 lean_s65, lean_s84, (Or (f True) (f False)), [1, (- 1)]
have lean_s86 : (Or (f True) (f False)) := by factor lean_s85, 1
let lean_s87 := by R2 lean_s20, lean_s86, (Or (f True) (f False)), [(- 1), 0]
have lean_s88 : (Eq True True) := rfl
have lean_s89 : True := eqResolve lean_s88 lean_r5
let lean_s90 := by R2 lean_s87, lean_s89, True, [(- 1), 0]
let lean_s91 := by R2 lean_s90, lean_s62, (f (Or (f True) (f False))), [(- 1), 0]
have lean_s92 : (Eq (f True) (f True)) := flipCongrArg lean_s68 [f]
have lean_s93 : (Eq (Not (f True)) (Not (f True))) := flipCongrArg lean_s92 [Not]
have lean_s94 : (Not (f True)) := eqResolve lean_a18 lean_s93
exact (show False from by R1 lean_s91, lean_s94, (f True), [0, 0])


