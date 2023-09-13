-- import Smt.Reconstruction.Certifying
open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000

variable {x0 : Prop}
variable {z0 : Prop}
variable {y0 : Prop}
variable {y1 : Prop}
variable {y0 : Prop}
variable {x0 : Prop}
variable {f : (Prop -> Prop)}
variable {z0 : Prop}
variable {x1 : Prop}
variable {f : (Prop -> Prop)}
variable {x1 : Prop}
variable {y1 : Prop}

theorem th0 : (Eq (Eq (f (Or x0 z0)) (f (Or x0 z0))) True) → (Eq (Eq True True) True) → (Eq (Eq y1 True) y1) → (Eq (Eq (Not (Not (f (Or x0 z0)))) (f (Or x0 z0))) (Eq (f (Or x0 z0)) (Not (Not (f (Or x0 z0)))))) → (Eq (Eq x1 True) x1) → (Eq (And True True) True) → (Eq (Not (Not (f (Or x0 z0)))) (f (Or x0 z0))) → (Eq (Eq (Or x0 z0) (Or x0 z0)) True) → (Eq (Eq (f (Or x0 z0)) (f True)) (Eq (f True) (f (Or x0 z0)))) → (Or x0 y0) → (Or (Not y0) z0) → x1 → y1 → (Not (Eq (f (Or x0 z0)) (f (And x1 y1)))) → False :=
fun lean_r0 : (Eq (Eq (f (Or x0 z0)) (f (Or x0 z0))) True) => -- THEORY_REWRITE_BOOL
fun lean_r1 : (Eq (Eq True True) True) => -- THEORY_REWRITE_BOOL
fun lean_r2 : (Eq (Eq y1 True) y1) => -- THEORY_REWRITE_BOOL
fun lean_r3 : (Eq (Eq (Not (Not (f (Or x0 z0)))) (f (Or x0 z0))) (Eq (f (Or x0 z0)) (Not (Not (f (Or x0 z0)))))) => -- THEORY_REWRITE_BOOL
fun lean_r4 : (Eq (Eq x1 True) x1) => -- THEORY_REWRITE_BOOL
fun lean_r5 : (Eq (And True True) True) => -- THEORY_REWRITE_BOOL
fun lean_r6 : (Eq (Not (Not (f (Or x0 z0)))) (f (Or x0 z0))) => -- THEORY_REWRITE_BOOL
fun lean_r7 : (Eq (Eq (Or x0 z0) (Or x0 z0)) True) => -- THEORY_REWRITE_BOOL
fun lean_r8 : (Eq (Eq (f (Or x0 z0)) (f True)) (Eq (f True) (f (Or x0 z0)))) => -- THEORY_REWRITE_BOOL
fun lean_a9 : (Or x0 y0) =>
fun lean_a10 : (Or (Not y0) z0) =>
fun lean_a11 : x1 =>
fun lean_a12 : y1 =>
fun lean_a13 : (Not (Eq (f (Or x0 z0)) (f (And x1 y1)))) => by
have lean_s0 : (Or z0 (Not y0)) := by permutateOr lean_a10, [1, 0], (- 1)
have lean_s1 : (Or (Or x0 z0) (Not x0)) := @cnfOrNeg [x0, z0] 0
have lean_s2 : (Eq (Eq (Or x0 z0) (Or x0 z0)) (Eq (Or x0 z0) (Or x0 z0))) := rfl
have lean_s3 : (Eq (Or x0 z0) (Or x0 z0)) := rfl
let lean_s4 := flipCongrArg lean_s3 [Eq]
have lean_s5 : (Eq (Or x0 z0) (Or x0 z0)) := rfl
have lean_s6 : (Eq (Eq (Or x0 z0) (Or x0 z0)) (Eq (Or x0 z0) (Or x0 z0))) := congr lean_s4 lean_s5
let lean_s7 := Eq.trans lean_s2 lean_s6
have lean_s8 : (Eq (Eq (Or x0 z0) (Or x0 z0)) True) := Eq.trans lean_s7 lean_r7
have lean_s9 : (Eq (Or x0 z0) (Or x0 z0)) := trueElim lean_s8
have lean_s10 : (Or (Not (Or x0 z0)) (Or x0 z0)) := equivElim1 lean_s9
have lean_s11 : (Or (Or x0 z0) (Not (Or x0 z0))) := by permutateOr lean_s10, [1, 0], 1
have lean_s12 : (Or (And (f (Or x0 z0)) (And (Or x0 z0) True)) (Or (Not (f (Or x0 z0))) (Or (Not (Or x0 z0)) (Not True)))) := cnfAndNeg [(f (Or x0 z0)), (Or x0 z0), True]
have lean_s13 : (Or (Not (f (Or x0 z0))) (Or (Not (Or x0 z0)) (Or (Not True) (f True)))) :=
  (scope (fun lean_a14 : (f (Or x0 z0)) =>
    (scope (fun lean_a15 : (Or x0 z0) =>
      (scope (fun lean_a16 : True =>
        have lean_s13 : (Eq True True) := rfl
        have lean_s14 : (Eq (Or x0 z0) True) := by timed trueIntro lean_a15
        have lean_s15 : (Eq True (Or x0 z0)) := Eq.symm lean_s14
        have lean_s16 : (Eq True (Or x0 z0)) := Eq.trans lean_s13 lean_s15
        have lean_s17 : (Eq (f True) (f (Or x0 z0))) := flipCongrArg lean_s16 [f]
        have lean_s18 : (Eq (f (Or x0 z0)) True) := trueIntro lean_a14
        have lean_s19 : (Eq (f True) True) := Eq.trans lean_s17 lean_s18
        have lean_s20 : (f True) := trueElim lean_s19
        show (f True) from lean_s20
  ))))))
have lean_s14 : (Implies (And (f (Or x0 z0)) (And (Or x0 z0) True)) (f True)) := by liftOrNToImp lean_s13, 3
have lean_s15 : (Or (Not (And (f (Or x0 z0)) (And (Or x0 z0) True))) (f True)) := impliesElim lean_s14
have lean_s16 : (Or (Not (f (Or x0 z0))) (Or (Not (Or x0 z0)) (Or (Not True) (f True)))) := by R1 lean_s12, lean_s15, (And (f (Or x0 z0)) (And (Or x0 z0) True)), [(- 1), (- 1)]
have lean_s17 : (Or (f True) (Or (Not (f (Or x0 z0))) (Or (Not True) (Not (Or x0 z0))))) := by permutateOr lean_s16, [3, 0, 2, 1], (- 1)
have lean_s18 : (Eq True True) := rfl
have lean_s19 : True := eqResolve lean_s18 lean_r1
let lean_s20 := by R2 lean_s17, lean_s19, True, [(- 1), 0]
have lean_s21 : (Eq (f (Or x0 z0)) (f (Or x0 z0))) := rfl
let lean_s22 := flipCongrArg lean_s21 [Eq]
have lean_s23 : (Eq y1 (Eq y1 True)) := Eq.symm lean_r2
have lean_s24 : (Eq y1 True) := eqResolve lean_a12 lean_s23
have lean_s25 : (Eq x1 (Eq x1 True)) := Eq.symm lean_r4
have lean_s26 : (Eq x1 True) := eqResolve lean_a11 lean_s25
have lean_s27 : (And (Eq y1 True) (Eq x1 True)) := And.intro lean_s24 lean_s26
have lean_s28 : (Eq x1 True) := by andElim lean_s27, 1
let lean_s29 := flipCongrArg lean_s28 [And]
have lean_s30 : (Eq y1 True) := by andElim lean_s27, 0
have lean_s31 : (Eq (And x1 y1) (And True True)) := congr lean_s29 lean_s30
have lean_s32 : (Eq (f (And x1 y1)) (f (And True True))) := flipCongrArg lean_s31 [f]
have lean_s33 : (Eq (Eq (f (Or x0 z0)) (f (And x1 y1))) (Eq (f (Or x0 z0)) (f (And True True)))) := congr lean_s22 lean_s32
have lean_s34 : (Eq (Not (Eq (f (Or x0 z0)) (f (And x1 y1)))) (Not (Eq (f (Or x0 z0)) (f (And True True))))) := flipCongrArg lean_s33 [Not]
have lean_s35 : (Eq (f (Or x0 z0)) (f (Or x0 z0))) := rfl
let lean_s36 := flipCongrArg lean_s35 [Eq]
have lean_s37 : (Eq (f (And True True)) (f True)) := flipCongrArg lean_r5 [f]
have lean_s38 : (Eq (Eq (f (Or x0 z0)) (f (And True True))) (Eq (f (Or x0 z0)) (f True))) := congr lean_s36 lean_s37
have lean_s39 : (Eq (Not (Eq (f (Or x0 z0)) (f (And True True)))) (Not (Eq (f (Or x0 z0)) (f True)))) := flipCongrArg lean_s38 [Not]
have lean_s40 : (Eq (Not (Eq (f (Or x0 z0)) (f (And x1 y1)))) (Not (Eq (f (Or x0 z0)) (f True)))) := Eq.trans lean_s34 lean_s39
have lean_s41 : (Eq (Or x0 z0) (Or x0 z0)) := trueElim lean_s8
have lean_s42 : (Eq (f (Or x0 z0)) (f (Or x0 z0))) := flipCongrArg lean_s41 [f]
let lean_s43 := flipCongrArg lean_s42 [Eq]
have lean_s44 : (Eq True True) := rfl
have lean_s45 : (Eq True True) := Eq.symm lean_s44
have lean_s46 : (Eq (f True) (f True)) := flipCongrArg lean_s45 [f]
have lean_s47 : (Eq (Eq (f (Or x0 z0)) (f True)) (Eq (f (Or x0 z0)) (f True))) := congr lean_s43 lean_s46
have lean_s48 : (Eq (Eq (f (Or x0 z0)) (f True)) (Eq (f True) (f (Or x0 z0)))) := Eq.trans lean_s47 lean_r8
have lean_s49 : (Eq (Not (Eq (f (Or x0 z0)) (f True))) (Not (Eq (f True) (f (Or x0 z0))))) := flipCongrArg lean_s48 [Not]
have lean_s50 : (Eq (Not (Eq (f (Or x0 z0)) (f (And x1 y1)))) (Not (Eq (f True) (f (Or x0 z0))))) := Eq.trans lean_s40 lean_s49
have lean_s51 : (Not (Eq (f True) (f (Or x0 z0)))) := eqResolve lean_a13 lean_s50
have lean_s52 : (Or (Not (f True)) (Not (f (Or x0 z0)))) := notEquivElim2 lean_s51
have lean_s53 : (Or (Not (f (Or x0 z0))) (Or (Not (Or x0 z0)) (Not (f (Or x0 z0))))) := by R1 lean_s20, lean_s52, (f True), [(- 1), (- 1)]
have lean_s54 : (Or (Not (f (Or x0 z0))) (Not (Or x0 z0))) := by factor lean_s53, 2
have lean_s55 : (Or (And (Not (f (Or x0 z0))) (And (Or x0 z0) True)) (Or (Not (Not (f (Or x0 z0)))) (Or (Not (Or x0 z0)) (Not True)))) := cnfAndNeg [(Not (f (Or x0 z0))), (Or x0 z0), True]
have lean_s56 : (Or (Not (Not (f (Or x0 z0)))) (Or (Not (Or x0 z0)) (Or (Not True) (Not (f True))))) :=
  (scope (fun lean_a17 : (Not (f (Or x0 z0))) =>
    (scope (fun lean_a18 : (Or x0 z0) =>
      (scope (fun lean_a19 : True =>
        have lean_s56 : (Eq True True) := rfl
        have lean_s57 : (Eq (Or x0 z0) True) := trueIntro lean_a18
        have lean_s58 : (Eq True (Or x0 z0)) := Eq.symm lean_s57
        have lean_s59 : (Eq True (Or x0 z0)) := Eq.trans lean_s56 lean_s58
        have lean_s60 : (Eq (f True) (f (Or x0 z0))) := flipCongrArg lean_s59 [f]
        have lean_s61 : (Eq (f (Or x0 z0)) False) := falseIntro lean_a17
        have lean_s62 : (Eq (f True) False) := Eq.trans lean_s60 lean_s61
        have lean_s63 : (Not (f True)) := falseElim lean_s62
        show (Not (f True)) from lean_s63
  ))))))
have lean_s57 : (Implies (And (Not (f (Or x0 z0))) (And (Or x0 z0) True)) (Not (f True))) := by liftOrNToImp lean_s56, 3
have lean_s58 : (Or (Not (And (Not (f (Or x0 z0))) (And (Or x0 z0) True))) (Not (f True))) := impliesElim lean_s57
have lean_s59 : (Or (Not (Not (f (Or x0 z0)))) (Or (Not (Or x0 z0)) (Or (Not True) (Not (f True))))) := by R1 lean_s55, lean_s58, (And (Not (f (Or x0 z0))) (And (Or x0 z0) True)), [(- 1), (- 1)]
have lean_s60 : (Eq Or Or) := rfl
have lean_s61 : (Eq (f (Or x0 z0)) (f (Or x0 z0))) := rfl
let lean_s62 := flipCongrArg lean_s61 [Eq]
have lean_s63 : (Eq (Eq (f (Or x0 z0)) (Not (Not (f (Or x0 z0))))) (Eq (f (Or x0 z0)) (f (Or x0 z0)))) := congr lean_s62 lean_r6
have lean_s64 : (Eq (Eq (f (Or x0 z0)) (Not (Not (f (Or x0 z0))))) True) := Eq.trans lean_s63 lean_r0
have lean_s65 : (Eq (Eq (Not (Not (f (Or x0 z0)))) (f (Or x0 z0))) True) := Eq.trans lean_r3 lean_s64
have lean_s66 : (Eq (Not (Not (f (Or x0 z0)))) (f (Or x0 z0))) := trueElim lean_s65
let lean_s67 := congr lean_s60 lean_s66
have lean_s68 : (Eq (Not (Or x0 z0)) (Not (Or x0 z0))) := rfl
let lean_s69 := congr lean_s60 lean_s68
have lean_s70 : (Eq (Not True) (Not True)) := rfl
let lean_s71 := congr lean_s60 lean_s70
have lean_s72 : (Eq (Not (f True)) (Not (f True))) := rfl
let lean_s73 := congr lean_s71 lean_s72
let lean_s74 := congr lean_s69 lean_s73
have lean_s75 : (Eq (Or (Not (Not (f (Or x0 z0)))) (Or (Not (Or x0 z0)) (Or (Not True) (Not (f True))))) (Or (f (Or x0 z0)) (Or (Not (Or x0 z0)) (Or (Not True) (Not (f True)))))) := congr lean_s67 lean_s74
have lean_s76 : (Or (f (Or x0 z0)) (Or (Not (Or x0 z0)) (Or (Not True) (Not (f True))))) := eqResolve lean_s59 lean_s75
have lean_s77 : (Or (f (Or x0 z0)) (Or (Not (f True)) (Or (Not True) (Not (Or x0 z0))))) := by permutateOr lean_s76, [0, 3, 2, 1], (- 1)
let lean_s78 := by R2 lean_s77, lean_s19, True, [(- 1), 0]
have lean_s79 : (Or (f True) (f (Or x0 z0))) := notEquivElim1 lean_s51
have lean_s80 : (Or (f (Or x0 z0)) (Or (Not (Or x0 z0)) (f (Or x0 z0)))) := by R2 lean_s78, lean_s79, (f True), [(- 1), (- 1)]
have lean_s81 : (Or (f (Or x0 z0)) (Not (Or x0 z0))) := by factor lean_s80, 2
have lean_s82 : (Or (Not (Or x0 z0)) (Not (Or x0 z0))) := by R2 lean_s54, lean_s81, (f (Or x0 z0)), [(- 1), (- 1)]
have lean_s83 : (Not (Or x0 z0)) := by factor lean_s82, 1
have lean_s84 : (Not (Or x0 z0)) := by R1 lean_s11, lean_s83, (Or x0 z0), [(- 1), 0]
have lean_s85 : (Not x0) := by R1 lean_s1, lean_s84, (Or x0 z0), [(- 1), 0]
have lean_s86 : y0 := by R1 lean_a9, lean_s85, x0, [(- 1), 0]
let lean_s87 := by R2 lean_s0, lean_s86, y0, [(- 1), 0]
have lean_s88 : (Or (Or x0 z0) (Not z0)) := @cnfOrNeg [x0, z0] 1
have lean_s89 : (Not z0) := by R1 lean_s88, lean_s84, (Or x0 z0), [(- 1), 0]
exact (show False from by R1 lean_s87, lean_s89, z0, [0, 0])


