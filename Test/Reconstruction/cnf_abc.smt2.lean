import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {I : Type u} [Nonempty I]
variable {a : I}
variable {f : (I -> I -> I)}
variable {b : I}
variable {f : (I -> I -> I)}
variable {c : I}
variable {c : I}
variable {b : I}
variable {a : I}

theorem th0 : (Or (Eq (f a a) a) (Eq (f a a) b)) → (Eq (Eq (f a a) c) (Eq c (f a a))) → (Eq (Eq (f b b) c) (Eq c (f b b))) → (Eq (Eq (f c c) c) (Eq c (f c c))) → (Eq (Eq (Not (Not (Eq (f b b) (f c b)))) (Eq (f b b) (f c b))) (Eq (Eq (f b b) (f c b)) (Not (Not (Eq (f b b) (f c b)))))) → (Eq (Eq (Eq (f b b) (f c b)) (Eq (f b b) (f c b))) True) → (Eq (Eq (Not (Not (Eq (f a b) (f b b)))) (Eq (f a b) (f b b))) (Eq (Eq (f a b) (f b b)) (Not (Not (Eq (f a b) (f b b)))))) → (Eq (Eq (f c c) a) (Eq a (f c c))) → (Eq (Not (Not (Eq (f b b) (f c b)))) (Eq (f b b) (f c b))) → (Eq (Not (Not (Eq (f a b) (f c b)))) (Eq (f a b) (f c b))) → (Eq (Eq (f c a) c) (Eq c (f c a))) → (Eq (Eq (Eq (f a b) (f c b)) (Eq (f a b) (f c b))) True) → (Eq (Eq (Not (Not (Eq (f a b) (f c b)))) (Eq (f a b) (f c b))) (Eq (Eq (f a b) (f c b)) (Not (Not (Eq (f a b) (f c b)))))) → (Eq (Eq (f a a) a) (Eq a (f a a))) → (Eq (Eq (f c b) c) (Eq c (f c b))) → (Eq (Not (Not (Eq (f a a) (f c a)))) (Eq (f a a) (f c a))) → (Eq (Eq (f a b) a) (Eq a (f a b))) → (Eq (Eq (f a a) b) (Eq b (f a a))) → (Eq (Eq (Eq (f a b) (f b b)) (Eq (f a b) (f b b))) True) → (Eq (Eq (f b b) b) (Eq b (f b b))) → (Eq (Not (Not (Eq (f a a) (f b a)))) (Eq (f a a) (f b a))) → (Eq (Eq (f c b) b) (Eq b (f c b))) → (Eq (Eq (f c b) a) (Eq a (f c b))) → (Eq (Eq (Not (Not (Eq (f a a) (f c a)))) (Eq (f a a) (f c a))) (Eq (Eq (f a a) (f c a)) (Not (Not (Eq (f a a) (f c a)))))) → (Eq (Eq (f c (f c a)) a) (Eq a (f c (f c a)))) → (Eq (Not (Not (Eq (f a b) (f b b)))) (Eq (f a b) (f b b))) → (Eq (Eq (f b b) a) (Eq a (f b b))) → (Eq (Eq (Eq (f a a) (f b a)) (Eq (f a a) (f b a))) True) → (Eq (Eq (Not (Not (Eq (f a a) (f b a)))) (Eq (f a a) (f b a))) (Eq (Eq (f a a) (f b a)) (Not (Not (Eq (f a a) (f b a)))))) → (Eq (Eq (f b a) b) (Eq b (f b a))) → (Eq (Eq (f c (f c c)) c) (Eq c (f c (f c c)))) → (Eq (Eq (Eq (f a a) (f c a)) (Eq (f a a) (f c a))) True) → (Eq (Eq (f c (f c b)) b) (Eq b (f c (f c b)))) → (Or (Eq (f a a) a) (Or (Eq (f a a) b) (Eq (f a a) c))) → (Or (Eq (f a b) a) (Or (Eq (f a b) b) (Eq (f a b) c))) → (Or (Eq (f a c) a) (Or (Eq (f a c) b) (Eq (f a c) c))) → (Or (Eq (f b a) a) (Or (Eq (f b a) b) (Eq (f b a) c))) → (Or (Eq (f b b) a) (Or (Eq (f b b) b) (Eq (f b b) c))) → (Or (Eq (f b c) a) (Or (Eq (f b c) b) (Eq (f b c) c))) → (Or (Eq (f c a) a) (Or (Eq (f c a) b) (Eq (f c a) c))) → (Or (Eq (f c b) a) (Or (Eq (f c b) b) (Eq (f c b) c))) → (Or (Eq (f c c) a) (Or (Eq (f c c) b) (Eq (f c c) c))) → (Or (Eq (f a a) a) (Or (Eq (f b b) a) (Eq (f c c) a))) → (Or (Eq (f a a) b) (Or (Eq (f b b) b) (Eq (f c c) b))) → (Or (Eq (f a a) c) (Or (Eq (f b b) c) (Eq (f c c) c))) → (Or (Eq (f a a) a) (Or (Eq (f b a) b) (Eq (f c a) c))) → (Or (Eq (f a b) a) (Or (Eq (f b b) b) (Eq (f c b) c))) → (Or (Eq (f a c) a) (Or (Eq (f b c) b) (Eq (f c c) c))) → (Not (Eq (f a a) a)) → (Not (Eq (f b b) b)) → (Not (Eq (f c c) c)) → (Or (Not (Eq (f a (f a a)) a)) (Or (Not (Eq (f a (f a b)) b)) (Not (Eq (f a (f a c)) c)))) → (Or (Not (Eq (f b (f b a)) a)) (Or (Not (Eq (f b (f b b)) b)) (Not (Eq (f b (f b c)) c)))) → (Or (Not (Eq (f c (f c a)) a)) (Or (Not (Eq (f c (f c b)) b)) (Not (Eq (f c (f c c)) c)))) → (Not (Eq (f a a) (f b a))) → (Not (Eq (f a a) (f c a))) → (Not (Eq (f b a) (f c a))) → (Not (Eq (f a b) (f b b))) → (Not (Eq (f a b) (f c b))) → (Not (Eq (f b b) (f c b))) → (Not (Eq (f a c) (f b c))) → (Not (Eq (f a c) (f c c))) → (Not (Eq (f b c) (f c c))) → False :=
fun lean_h0 : (Or (Eq (f a a) a) (Eq (f a a) b)) =>
fun lean_r1 : (Eq (Eq (f a a) c) (Eq c (f a a))) =>
fun lean_r2 : (Eq (Eq (f b b) c) (Eq c (f b b))) =>
fun lean_r3 : (Eq (Eq (f c c) c) (Eq c (f c c))) =>
fun lean_r4 : (Eq (Eq (Not (Not (Eq (f b b) (f c b)))) (Eq (f b b) (f c b))) (Eq (Eq (f b b) (f c b)) (Not (Not (Eq (f b b) (f c b)))))) =>
fun lean_r5 : (Eq (Eq (Eq (f b b) (f c b)) (Eq (f b b) (f c b))) True) =>
fun lean_r6 : (Eq (Eq (Not (Not (Eq (f a b) (f b b)))) (Eq (f a b) (f b b))) (Eq (Eq (f a b) (f b b)) (Not (Not (Eq (f a b) (f b b)))))) =>
fun lean_r7 : (Eq (Eq (f c c) a) (Eq a (f c c))) =>
fun lean_r8 : (Eq (Not (Not (Eq (f b b) (f c b)))) (Eq (f b b) (f c b))) =>
fun lean_r9 : (Eq (Not (Not (Eq (f a b) (f c b)))) (Eq (f a b) (f c b))) =>
fun lean_r10 : (Eq (Eq (f c a) c) (Eq c (f c a))) =>
fun lean_r11 : (Eq (Eq (Eq (f a b) (f c b)) (Eq (f a b) (f c b))) True) =>
fun lean_r12 : (Eq (Eq (Not (Not (Eq (f a b) (f c b)))) (Eq (f a b) (f c b))) (Eq (Eq (f a b) (f c b)) (Not (Not (Eq (f a b) (f c b)))))) =>
fun lean_r13 : (Eq (Eq (f a a) a) (Eq a (f a a))) =>
fun lean_r14 : (Eq (Eq (f c b) c) (Eq c (f c b))) =>
fun lean_r15 : (Eq (Not (Not (Eq (f a a) (f c a)))) (Eq (f a a) (f c a))) =>
fun lean_r16 : (Eq (Eq (f a b) a) (Eq a (f a b))) =>
fun lean_r17 : (Eq (Eq (f a a) b) (Eq b (f a a))) =>
fun lean_r18 : (Eq (Eq (Eq (f a b) (f b b)) (Eq (f a b) (f b b))) True) =>
fun lean_r19 : (Eq (Eq (f b b) b) (Eq b (f b b))) =>
fun lean_r20 : (Eq (Not (Not (Eq (f a a) (f b a)))) (Eq (f a a) (f b a))) =>
fun lean_r21 : (Eq (Eq (f c b) b) (Eq b (f c b))) =>
fun lean_r22 : (Eq (Eq (f c b) a) (Eq a (f c b))) =>
fun lean_r23 : (Eq (Eq (Not (Not (Eq (f a a) (f c a)))) (Eq (f a a) (f c a))) (Eq (Eq (f a a) (f c a)) (Not (Not (Eq (f a a) (f c a)))))) =>
fun lean_r24 : (Eq (Eq (f c (f c a)) a) (Eq a (f c (f c a)))) =>
fun lean_r25 : (Eq (Not (Not (Eq (f a b) (f b b)))) (Eq (f a b) (f b b))) =>
fun lean_r26 : (Eq (Eq (f b b) a) (Eq a (f b b))) =>
fun lean_r27 : (Eq (Eq (Eq (f a a) (f b a)) (Eq (f a a) (f b a))) True) =>
fun lean_r28 : (Eq (Eq (Not (Not (Eq (f a a) (f b a)))) (Eq (f a a) (f b a))) (Eq (Eq (f a a) (f b a)) (Not (Not (Eq (f a a) (f b a)))))) =>
fun lean_r29 : (Eq (Eq (f b a) b) (Eq b (f b a))) =>
fun lean_r30 : (Eq (Eq (f c (f c c)) c) (Eq c (f c (f c c)))) =>
fun lean_r31 : (Eq (Eq (Eq (f a a) (f c a)) (Eq (f a a) (f c a))) True) =>
fun lean_r32 : (Eq (Eq (f c (f c b)) b) (Eq b (f c (f c b)))) =>
fun lean_a33 : (Or (Eq (f a a) a) (Or (Eq (f a a) b) (Eq (f a a) c))) =>
fun lean_a34 : (Or (Eq (f a b) a) (Or (Eq (f a b) b) (Eq (f a b) c))) =>
fun lean_a35 : (Or (Eq (f a c) a) (Or (Eq (f a c) b) (Eq (f a c) c))) =>
fun lean_a36 : (Or (Eq (f b a) a) (Or (Eq (f b a) b) (Eq (f b a) c))) =>
fun lean_a37 : (Or (Eq (f b b) a) (Or (Eq (f b b) b) (Eq (f b b) c))) =>
fun lean_a38 : (Or (Eq (f b c) a) (Or (Eq (f b c) b) (Eq (f b c) c))) =>
fun lean_a39 : (Or (Eq (f c a) a) (Or (Eq (f c a) b) (Eq (f c a) c))) =>
fun lean_a40 : (Or (Eq (f c b) a) (Or (Eq (f c b) b) (Eq (f c b) c))) =>
fun lean_a41 : (Or (Eq (f c c) a) (Or (Eq (f c c) b) (Eq (f c c) c))) =>
fun lean_a42 : (Or (Eq (f a a) a) (Or (Eq (f b b) a) (Eq (f c c) a))) =>
fun lean_a43 : (Or (Eq (f a a) b) (Or (Eq (f b b) b) (Eq (f c c) b))) =>
fun lean_a44 : (Or (Eq (f a a) c) (Or (Eq (f b b) c) (Eq (f c c) c))) =>
fun lean_a45 : (Or (Eq (f a a) a) (Or (Eq (f b a) b) (Eq (f c a) c))) =>
fun lean_a46 : (Or (Eq (f a b) a) (Or (Eq (f b b) b) (Eq (f c b) c))) =>
fun lean_a47 : (Or (Eq (f a c) a) (Or (Eq (f b c) b) (Eq (f c c) c))) =>
fun lean_a48 : (Not (Eq (f a a) a)) =>
fun lean_a49 : (Not (Eq (f b b) b)) =>
fun lean_a50 : (Not (Eq (f c c) c)) =>
fun lean_a51 : (Or (Not (Eq (f a (f a a)) a)) (Or (Not (Eq (f a (f a b)) b)) (Not (Eq (f a (f a c)) c)))) =>
fun lean_a52 : (Or (Not (Eq (f b (f b a)) a)) (Or (Not (Eq (f b (f b b)) b)) (Not (Eq (f b (f b c)) c)))) =>
fun lean_a53 : (Or (Not (Eq (f c (f c a)) a)) (Or (Not (Eq (f c (f c b)) b)) (Not (Eq (f c (f c c)) c)))) =>
fun lean_a54 : (Not (Eq (f a a) (f b a))) =>
fun lean_a55 : (Not (Eq (f a a) (f c a))) =>
fun lean_a56 : (Not (Eq (f b a) (f c a))) =>
fun lean_a57 : (Not (Eq (f a b) (f b b))) =>
fun lean_a58 : (Not (Eq (f a b) (f c b))) =>
fun lean_a59 : (Not (Eq (f b b) (f c b))) =>
fun lean_a60 : (Not (Eq (f a c) (f b c))) =>
fun lean_a61 : (Not (Eq (f a c) (f c c))) =>
fun lean_a62 : (Not (Eq (f b c) (f c c))) => by
have lean_s0 : (Or (And (Eq c (f c b)) (And (Eq c (f a a)) (Eq b (f a a)))) (Or (Not (Eq c (f c b))) (Or (Not (Eq c (f a a))) (Not (Eq b (f a a)))))) := cnfAndNeg [(Eq c (f c b)), (Eq c (f a a)), (Eq b (f a a))]
have lean_s1 : (Or (Not (Eq c (f c b))) (Or (Not (Eq c (f a a))) (Or (Not (Eq b (f a a))) (Eq b (f c b))))) :=
  (scope (fun lean_a63 : (Eq c (f c b)) =>
    (scope (fun lean_a64 : (Eq c (f a a)) =>
      (scope (fun lean_a65 : (Eq b (f a a)) =>
        have lean_s1 : (Eq (f a a) b) := Eq.symm lean_a65
        have lean_s2 : (Eq b (f a a)) := Eq.symm lean_s1
        have lean_s3 : (Eq (f a a) c) := Eq.symm lean_a64
        let lean_s4 := Eq.trans lean_s2 lean_s3
        have lean_s5 : (Eq (f c b) c) := Eq.symm lean_a63
        have lean_s6 : (Eq c (f c b)) := Eq.symm lean_s5
        have lean_s7 : (Eq b (f c b)) := Eq.trans lean_s4 lean_s6
        show (Eq b (f c b)) from lean_s7
  ))))))
have lean_s2 : (Implies (And (Eq c (f c b)) (And (Eq c (f a a)) (Eq b (f a a)))) (Eq b (f c b))) := by liftOrNToImp lean_s1, 3
have lean_s3 : (Or (Not (And (Eq c (f c b)) (And (Eq c (f a a)) (Eq b (f a a))))) (Eq b (f c b))) := impliesElim lean_s2
have lean_s4 : (Or (Not (Eq c (f c b))) (Or (Not (Eq c (f a a))) (Or (Not (Eq b (f a a))) (Eq b (f c b))))) := by R1 lean_s0, lean_s3, (And (Eq c (f c b)) (And (Eq c (f a a)) (Eq b (f a a)))), [(- 1), (- 1)]
have lean_s5 : (Or (Eq b (f c b)) (Or (Not (Eq b (f a a))) (Or (Not (Eq c (f a a))) (Not (Eq c (f c b)))))) := by permutateOr lean_s4, [3, 2, 1, 0], (- 1)
have lean_s6 : (Or (And (Not (Eq (f a a) (f c a))) (And (Eq b (f a a)) (And (Eq c (f c a)) (Eq c (f c b))))) (Or (Not (Not (Eq (f a a) (f c a)))) (Or (Not (Eq b (f a a))) (Or (Not (Eq c (f c a))) (Not (Eq c (f c b))))))) := cnfAndNeg [(Not (Eq (f a a) (f c a))), (Eq b (f a a)), (Eq c (f c a)), (Eq c (f c b))]
have lean_s7 : (Or (Not (Not (Eq (f a a) (f c a)))) (Or (Not (Eq b (f a a))) (Or (Not (Eq c (f c a))) (Or (Not (Eq c (f c b))) (Not (Eq b (f c b))))))) :=
  (scope (fun lean_a66 : (Not (Eq (f a a) (f c a))) =>
    (scope (fun lean_a67 : (Eq b (f a a)) =>
      (scope (fun lean_a68 : (Eq c (f c a)) =>
        (scope (fun lean_a69 : (Eq c (f c b)) =>
          have lean_s7 : (Eq (f a a) b) := Eq.symm lean_a67
          have lean_s8 : (Eq b (f a a)) := Eq.symm lean_s7
          let lean_s9 := flipCongrArg lean_s8 [Eq]
          have lean_s10 : (Eq (f c b) c) := Eq.symm lean_a69
          have lean_s11 : (Eq c (f c b)) := Eq.symm lean_s10
          have lean_s12 : (Eq (f c b) c) := Eq.symm lean_s11
          have lean_s13 : (Eq (f c a) c) := Eq.symm lean_a68
          have lean_s14 : (Eq c (f c a)) := Eq.symm lean_s13
          have lean_s15 : (Eq (f c b) (f c a)) := Eq.trans lean_s12 lean_s14
          have lean_s16 : (Eq (Eq b (f c b)) (Eq (f a a) (f c a))) := congr lean_s9 lean_s15
          have lean_s17 : (Eq (Eq (f a a) (f c a)) False) := falseIntro lean_a66
          have lean_s18 : (Eq (Eq b (f c b)) False) := Eq.trans lean_s16 lean_s17
          have lean_s19 : (Not (Eq b (f c b))) := falseElim lean_s18
          show (Not (Eq b (f c b))) from lean_s19
  ))))))))
have lean_s8 : (Implies (And (Not (Eq (f a a) (f c a))) (And (Eq b (f a a)) (And (Eq c (f c a)) (Eq c (f c b))))) (Not (Eq b (f c b)))) := by liftOrNToImp lean_s7, 4
have lean_s9 : (Or (Not (And (Not (Eq (f a a) (f c a))) (And (Eq b (f a a)) (And (Eq c (f c a)) (Eq c (f c b)))))) (Not (Eq b (f c b)))) := impliesElim lean_s8
have lean_s10 : (Or (Not (Not (Eq (f a a) (f c a)))) (Or (Not (Eq b (f a a))) (Or (Not (Eq c (f c a))) (Or (Not (Eq c (f c b))) (Not (Eq b (f c b))))))) := by R1 lean_s6, lean_s9, (And (Not (Eq (f a a) (f c a))) (And (Eq b (f a a)) (And (Eq c (f c a)) (Eq c (f c b))))), [(- 1), (- 1)]
have lean_s11 : (Eq Or Or) := rfl
have lean_s12 : (Eq (Eq (f a a) (f c a)) (Eq (f a a) (f c a))) := rfl
let lean_s13 := flipCongrArg lean_s12 [Eq]
have lean_s14 : (Eq (Eq (Eq (f a a) (f c a)) (Not (Not (Eq (f a a) (f c a))))) (Eq (Eq (f a a) (f c a)) (Eq (f a a) (f c a)))) := congr lean_s13 lean_r15
have lean_s15 : (Eq (Eq (Eq (f a a) (f c a)) (Not (Not (Eq (f a a) (f c a))))) True) := Eq.trans lean_s14 lean_r31
have lean_s16 : (Eq (Eq (Not (Not (Eq (f a a) (f c a)))) (Eq (f a a) (f c a))) True) := Eq.trans lean_r23 lean_s15
have lean_s17 : (Eq (Not (Not (Eq (f a a) (f c a)))) (Eq (f a a) (f c a))) := trueElim lean_s16
let lean_s18 := congr lean_s11 lean_s17
have lean_s19 : (Eq (Not (Eq b (f a a))) (Not (Eq b (f a a)))) := rfl
let lean_s20 := congr lean_s11 lean_s19
have lean_s21 : (Eq (Not (Eq c (f c a))) (Not (Eq c (f c a)))) := rfl
let lean_s22 := congr lean_s11 lean_s21
have lean_s23 : (Eq (Not (Eq c (f c b))) (Not (Eq c (f c b)))) := rfl
let lean_s24 := congr lean_s11 lean_s23
have lean_s25 : (Eq (Not (Eq b (f c b))) (Not (Eq b (f c b)))) := rfl
let lean_s26 := congr lean_s24 lean_s25
let lean_s27 := congr lean_s22 lean_s26
let lean_s28 := congr lean_s20 lean_s27
have lean_s29 : (Eq (Or (Not (Not (Eq (f a a) (f c a)))) (Or (Not (Eq b (f a a))) (Or (Not (Eq c (f c a))) (Or (Not (Eq c (f c b))) (Not (Eq b (f c b))))))) (Or (Eq (f a a) (f c a)) (Or (Not (Eq b (f a a))) (Or (Not (Eq c (f c a))) (Or (Not (Eq c (f c b))) (Not (Eq b (f c b)))))))) := congr lean_s18 lean_s28
have lean_s30 : (Or (Eq (f a a) (f c a)) (Or (Not (Eq b (f a a))) (Or (Not (Eq c (f c a))) (Or (Not (Eq c (f c b))) (Not (Eq b (f c b))))))) := eqResolve lean_s10 lean_s29
have lean_s31 : (Or (Eq (f a a) (f c a)) (Or (Not (Eq b (f a a))) (Or (Not (Eq c (f c a))) (Or (Not (Eq b (f c b))) (Not (Eq c (f c b))))))) := by permutateOr lean_s30, [0, 1, 2, 4, 3], (- 1)
let lean_s32 := by R1 lean_s31, lean_a55, (Eq (f a a) (f c a)), [(- 1), 0]
let lean_s33 := flipCongrArg lean_r13 [Or]
have lean_s34 : (Eq (Or (Eq (f a a) a) (Eq (f a a) b)) (Or (Eq a (f a a)) (Eq b (f a a)))) := congr lean_s33 lean_r17
have lean_s35 : (Or (Eq a (f a a)) (Eq b (f a a))) := eqResolve lean_h0 lean_s34
have lean_s36 : (Not (Eq a (f a a))) := negSymm lean_a48
have lean_s37 : (Eq b (f a a)) := by R1 lean_s35, lean_s36, (Eq a (f a a)), [(- 1), 0]
let lean_s38 := by R2 lean_s32, lean_s37, (Eq b (f a a)), [(- 1), 0]
have lean_s39 : (Eq Or Or) := rfl
let lean_s40 := congr lean_s39 lean_r13
let lean_s41 := congr lean_s39 lean_r29
let lean_s42 := congr lean_s41 lean_r10
have lean_s43 : (Eq (Or (Eq (f a a) a) (Or (Eq (f b a) b) (Eq (f c a) c))) (Or (Eq a (f a a)) (Or (Eq b (f b a)) (Eq c (f c a))))) := congr lean_s40 lean_s42
have lean_s44 : (Or (Eq a (f a a)) (Or (Eq b (f b a)) (Eq c (f c a)))) := eqResolve lean_a45 lean_s43
have lean_s45 : (Not (Eq a (f a a))) := negSymm lean_a48
let lean_s46 := by R1 lean_s44, lean_s45, (Eq a (f a a)), [(- 1), 0]
have lean_s47 : (Or (And (Not (Eq (f a a) (f b a))) (Eq b (f a a))) (Or (Not (Not (Eq (f a a) (f b a)))) (Not (Eq b (f a a))))) := cnfAndNeg [(Not (Eq (f a a) (f b a))), (Eq b (f a a))]
have lean_s48 : (Or (Not (Not (Eq (f a a) (f b a)))) (Or (Not (Eq b (f a a))) (Not (Eq b (f b a))))) :=
  (scope (fun lean_a67 : (Not (Eq (f a a) (f b a))) =>
    (scope (fun lean_a68 : (Eq b (f a a)) =>
      have lean_s48 : (Eq (f a a) b) := Eq.symm lean_a68
      have lean_s49 : (Eq b (f a a)) := Eq.symm lean_s48
      let lean_s50 := flipCongrArg lean_s49 [Eq]
      have lean_s51 : (Eq (f b a) (f b a)) := rfl
      have lean_s52 : (Eq (Eq b (f b a)) (Eq (f a a) (f b a))) := congr lean_s50 lean_s51
      have lean_s53 : (Eq (Eq (f a a) (f b a)) False) := falseIntro lean_a67
      have lean_s54 : (Eq (Eq b (f b a)) False) := Eq.trans lean_s52 lean_s53
      have lean_s55 : (Not (Eq b (f b a))) := falseElim lean_s54
      show (Not (Eq b (f b a))) from lean_s55
  ))))
have lean_s49 : (Implies (And (Not (Eq (f a a) (f b a))) (Eq b (f a a))) (Not (Eq b (f b a)))) := by liftOrNToImp lean_s48, 2
have lean_s50 : (Or (Not (And (Not (Eq (f a a) (f b a))) (Eq b (f a a)))) (Not (Eq b (f b a)))) := impliesElim lean_s49
have lean_s51 : (Or (Not (Not (Eq (f a a) (f b a)))) (Or (Not (Eq b (f a a))) (Not (Eq b (f b a))))) := by R1 lean_s47, lean_s50, (And (Not (Eq (f a a) (f b a))) (Eq b (f a a))), [(- 1), (- 1)]
have lean_s52 : (Eq Or Or) := rfl
have lean_s53 : (Eq (Eq (f a a) (f b a)) (Eq (f a a) (f b a))) := rfl
let lean_s54 := flipCongrArg lean_s53 [Eq]
have lean_s55 : (Eq (Eq (Eq (f a a) (f b a)) (Not (Not (Eq (f a a) (f b a))))) (Eq (Eq (f a a) (f b a)) (Eq (f a a) (f b a)))) := congr lean_s54 lean_r20
have lean_s56 : (Eq (Eq (Eq (f a a) (f b a)) (Not (Not (Eq (f a a) (f b a))))) True) := Eq.trans lean_s55 lean_r27
have lean_s57 : (Eq (Eq (Not (Not (Eq (f a a) (f b a)))) (Eq (f a a) (f b a))) True) := Eq.trans lean_r28 lean_s56
have lean_s58 : (Eq (Not (Not (Eq (f a a) (f b a)))) (Eq (f a a) (f b a))) := trueElim lean_s57
let lean_s59 := congr lean_s52 lean_s58
let lean_s60 := congr lean_s52 lean_s19
have lean_s61 : (Eq (Not (Eq b (f b a))) (Not (Eq b (f b a)))) := rfl
let lean_s62 := congr lean_s60 lean_s61
have lean_s63 : (Eq (Or (Not (Not (Eq (f a a) (f b a)))) (Or (Not (Eq b (f a a))) (Not (Eq b (f b a))))) (Or (Eq (f a a) (f b a)) (Or (Not (Eq b (f a a))) (Not (Eq b (f b a)))))) := congr lean_s59 lean_s62
have lean_s64 : (Or (Eq (f a a) (f b a)) (Or (Not (Eq b (f a a))) (Not (Eq b (f b a))))) := eqResolve lean_s51 lean_s63
let lean_s65 := by R1 lean_s64, lean_a54, (Eq (f a a) (f b a)), [(- 1), 0]
have lean_s66 : (Not (Eq b (f b a))) := by R2 lean_s65, lean_s37, (Eq b (f a a)), [(- 1), 0]
have lean_s67 : (Eq c (f c a)) := by R1 lean_s46, lean_s66, (Eq b (f b a)), [(- 1), 0]
let lean_s68 := by R2 lean_s38, lean_s67, (Eq c (f c a)), [(- 1), 0]
have lean_s69 : (Eq Or Or) := rfl
have lean_s70 : (Eq (Not (Eq (f c (f c a)) a)) (Not (Eq a (f c (f c a))))) := flipCongrArg lean_r24 [Not]
let lean_s71 := congr lean_s69 lean_s70
have lean_s72 : (Eq (Not (Eq (f c (f c b)) b)) (Not (Eq b (f c (f c b))))) := flipCongrArg lean_r32 [Not]
let lean_s73 := congr lean_s69 lean_s72
have lean_s74 : (Eq (Not (Eq (f c (f c c)) c)) (Not (Eq c (f c (f c c))))) := flipCongrArg lean_r30 [Not]
let lean_s75 := congr lean_s73 lean_s74
have lean_s76 : (Eq (Or (Not (Eq (f c (f c a)) a)) (Or (Not (Eq (f c (f c b)) b)) (Not (Eq (f c (f c c)) c)))) (Or (Not (Eq a (f c (f c a)))) (Or (Not (Eq b (f c (f c b)))) (Not (Eq c (f c (f c c))))))) := congr lean_s71 lean_s75
have lean_s77 : (Or (Not (Eq a (f c (f c a)))) (Or (Not (Eq b (f c (f c b)))) (Not (Eq c (f c (f c c)))))) := eqResolve lean_a53 lean_s76
have lean_s78 : (Or (And (Eq a (f c c)) (Eq c (f c a))) (Or (Not (Eq a (f c c))) (Not (Eq c (f c a))))) := cnfAndNeg [(Eq a (f c c)), (Eq c (f c a))]
have lean_s79 : (Or (Not (Eq a (f c c))) (Or (Not (Eq c (f c a))) (Eq c (f c (f c c))))) :=
  (scope (fun lean_a67 : (Eq a (f c c)) =>
    (scope (fun lean_a68 : (Eq c (f c a)) =>
      have lean_s79 : (Eq (f c a) c) := Eq.symm lean_a68
      have lean_s80 : (Eq c (f c a)) := Eq.symm lean_s79
      have lean_s81 : (Eq c c) := rfl
      let lean_s82 := flipCongrArg lean_s81 [f]
      have lean_s83 : (Eq (f c c) a) := Eq.symm lean_a67
      have lean_s84 : (Eq a (f c c)) := Eq.symm lean_s83
      have lean_s85 : (Eq (f c a) (f c (f c c))) := congr lean_s82 lean_s84
      have lean_s86 : (Eq c (f c (f c c))) := Eq.trans lean_s80 lean_s85
      show (Eq c (f c (f c c))) from lean_s86
  ))))
have lean_s80 : (Implies (And (Eq a (f c c)) (Eq c (f c a))) (Eq c (f c (f c c)))) := by liftOrNToImp lean_s79, 2
have lean_s81 : (Or (Not (And (Eq a (f c c)) (Eq c (f c a)))) (Eq c (f c (f c c)))) := impliesElim lean_s80
have lean_s82 : (Or (Not (Eq a (f c c))) (Or (Not (Eq c (f c a))) (Eq c (f c (f c c))))) := by R1 lean_s78, lean_s81, (And (Eq a (f c c)) (Eq c (f c a))), [(- 1), (- 1)]
have lean_s83 : (Or (Eq c (f c (f c c))) (Or (Not (Eq c (f c a))) (Not (Eq a (f c c))))) := by permutateOr lean_s82, [2, 1, 0], (- 1)
let lean_s84 := by R2 lean_s77, lean_s83, (Eq c (f c (f c c))), [(- 1), (- 1)]
let lean_s85 := by R2 lean_s84, lean_s67, (Eq c (f c a)), [(- 1), 0]
have lean_s86 : (Or (And (Eq c (f c a)) (Eq a (f c c))) (Or (Not (Eq c (f c a))) (Not (Eq a (f c c))))) := cnfAndNeg [(Eq c (f c a)), (Eq a (f c c))]
have lean_s87 : (Or (Not (Eq c (f c a))) (Or (Not (Eq a (f c c))) (Eq a (f c (f c a))))) :=
  (scope (fun lean_a68 : (Eq c (f c a)) =>
    (scope (fun lean_a69 : (Eq a (f c c)) =>
      have lean_s87 : (Eq (f c c) a) := Eq.symm lean_a69
      have lean_s88 : (Eq a (f c c)) := Eq.symm lean_s87
      have lean_s89 : (Eq c c) := rfl
      let lean_s90 := flipCongrArg lean_s89 [f]
      have lean_s91 : (Eq (f c a) c) := Eq.symm lean_a68
      have lean_s92 : (Eq c (f c a)) := Eq.symm lean_s91
      have lean_s93 : (Eq (f c c) (f c (f c a))) := congr lean_s90 lean_s92
      have lean_s94 : (Eq a (f c (f c a))) := Eq.trans lean_s88 lean_s93
      show (Eq a (f c (f c a))) from lean_s94
  ))))
have lean_s88 : (Implies (And (Eq c (f c a)) (Eq a (f c c))) (Eq a (f c (f c a)))) := by liftOrNToImp lean_s87, 2
have lean_s89 : (Or (Not (And (Eq c (f c a)) (Eq a (f c c)))) (Eq a (f c (f c a)))) := impliesElim lean_s88
have lean_s90 : (Or (Not (Eq c (f c a))) (Or (Not (Eq a (f c c))) (Eq a (f c (f c a))))) := by R1 lean_s86, lean_s89, (And (Eq c (f c a)) (Eq a (f c c))), [(- 1), (- 1)]
have lean_s91 : (Or (Eq a (f c (f c a))) (Or (Not (Eq c (f c a))) (Not (Eq a (f c c))))) := by permutateOr lean_s90, [2, 0, 1], (- 1)
let lean_s92 := by R2 lean_s85, lean_s91, (Eq a (f c (f c a))), [(- 1), (- 1)]
let lean_s93 := by R2 lean_s92, lean_s67, (Eq c (f c a)), [(- 1), 0]
have lean_s94 : (Or (Not (Eq b (f c b))) (Eq b (f c (f c b)))) :=
  (scope (fun lean_a68 : (Eq b (f c b)) =>
    have lean_s94 : (Eq (f c b) b) := Eq.symm lean_a68
    have lean_s95 : (Eq b (f c b)) := Eq.symm lean_s94
    have lean_s96 : (Eq c c) := rfl
    let lean_s97 := flipCongrArg lean_s96 [f]
    have lean_s98 : (Eq (f c b) (f c (f c b))) := congr lean_s97 lean_s95
    have lean_s99 : (Eq b (f c (f c b))) := Eq.trans lean_s95 lean_s98
    show (Eq b (f c (f c b))) from lean_s99
  ))
have lean_s95 : (Implies (Eq b (f c b)) (Eq b (f c (f c b)))) := by liftOrNToImp lean_s94, 1
have lean_s96 : (Or (Not (Eq b (f c b))) (Eq b (f c (f c b)))) := impliesElim lean_s95
have lean_s97 : (Or (Eq b (f c (f c b))) (Not (Eq b (f c b)))) := by permutateOr lean_s96, [1, 0], (- 1)
have lean_s98 : (Or (Not (Eq a (f c c))) (Or (Not (Eq a (f c c))) (Not (Eq b (f c b))))) := by R2 lean_s93, lean_s97, (Eq b (f c (f c b))), [(- 1), (- 1)]
have lean_s99 : (Or (Not (Eq a (f c c))) (Not (Eq b (f c b)))) := by factor lean_s98, (- 1)
have lean_s100 : (Eq Or Or) := rfl
let lean_s101 := congr lean_s100 lean_r13
let lean_s102 := congr lean_s100 lean_r26
let lean_s103 := congr lean_s102 lean_r7
have lean_s104 : (Eq (Or (Eq (f a a) a) (Or (Eq (f b b) a) (Eq (f c c) a))) (Or (Eq a (f a a)) (Or (Eq a (f b b)) (Eq a (f c c))))) := congr lean_s101 lean_s103
have lean_s105 : (Or (Eq a (f a a)) (Or (Eq a (f b b)) (Eq a (f c c)))) := eqResolve lean_a42 lean_s104
let lean_s106 := by R2 lean_s99, lean_s105, (Eq a (f c c)), [(- 1), (- 1)]
have lean_s107 : (Not (Eq a (f a a))) := negSymm lean_a48
let lean_s108 := by R1 lean_s106, lean_s107, (Eq a (f a a)), [(- 1), 0]
have lean_s109 : (Eq Or Or) := rfl
let lean_s110 := congr lean_s109 lean_r22
let lean_s111 := congr lean_s109 lean_r21
let lean_s112 := congr lean_s111 lean_r14
have lean_s113 : (Eq (Or (Eq (f c b) a) (Or (Eq (f c b) b) (Eq (f c b) c))) (Or (Eq a (f c b)) (Or (Eq b (f c b)) (Eq c (f c b))))) := congr lean_s110 lean_s112
have lean_s114 : (Or (Eq a (f c b)) (Or (Eq b (f c b)) (Eq c (f c b)))) := eqResolve lean_a40 lean_s113
let lean_s115 := by R2 lean_s108, lean_s114, (Eq b (f c b)), [(- 1), (- 1)]
have lean_s116 : (Or (And (Not (Eq (f a b) (f b b))) (Eq a (f a b))) (Or (Not (Not (Eq (f a b) (f b b)))) (Not (Eq a (f a b))))) := cnfAndNeg [(Not (Eq (f a b) (f b b))), (Eq a (f a b))]
have lean_s117 : (Or (Not (Not (Eq (f a b) (f b b)))) (Or (Not (Eq a (f a b))) (Not (Eq a (f b b))))) :=
  (scope (fun lean_a69 : (Not (Eq (f a b) (f b b))) =>
    (scope (fun lean_a70 : (Eq a (f a b)) =>
      have lean_s117 : (Eq (f a b) a) := Eq.symm lean_a70
      have lean_s118 : (Eq a (f a b)) := Eq.symm lean_s117
      let lean_s119 := flipCongrArg lean_s118 [Eq]
      have lean_s120 : (Eq (f b b) (f b b)) := rfl
      have lean_s121 : (Eq (Eq a (f b b)) (Eq (f a b) (f b b))) := congr lean_s119 lean_s120
      have lean_s122 : (Eq (Eq (f a b) (f b b)) False) := falseIntro lean_a69
      have lean_s123 : (Eq (Eq a (f b b)) False) := Eq.trans lean_s121 lean_s122
      have lean_s124 : (Not (Eq a (f b b))) := falseElim lean_s123
      show (Not (Eq a (f b b))) from lean_s124
  ))))
have lean_s118 : (Implies (And (Not (Eq (f a b) (f b b))) (Eq a (f a b))) (Not (Eq a (f b b)))) := by liftOrNToImp lean_s117, 2
have lean_s119 : (Or (Not (And (Not (Eq (f a b) (f b b))) (Eq a (f a b)))) (Not (Eq a (f b b)))) := impliesElim lean_s118
have lean_s120 : (Or (Not (Not (Eq (f a b) (f b b)))) (Or (Not (Eq a (f a b))) (Not (Eq a (f b b))))) := by R1 lean_s116, lean_s119, (And (Not (Eq (f a b) (f b b))) (Eq a (f a b))), [(- 1), (- 1)]
have lean_s121 : (Eq Or Or) := rfl
have lean_s122 : (Eq (Eq (f a b) (f b b)) (Eq (f a b) (f b b))) := rfl
let lean_s123 := flipCongrArg lean_s122 [Eq]
have lean_s124 : (Eq (Eq (Eq (f a b) (f b b)) (Not (Not (Eq (f a b) (f b b))))) (Eq (Eq (f a b) (f b b)) (Eq (f a b) (f b b)))) := congr lean_s123 lean_r25
have lean_s125 : (Eq (Eq (Eq (f a b) (f b b)) (Not (Not (Eq (f a b) (f b b))))) True) := Eq.trans lean_s124 lean_r18
have lean_s126 : (Eq (Eq (Not (Not (Eq (f a b) (f b b)))) (Eq (f a b) (f b b))) True) := Eq.trans lean_r6 lean_s125
have lean_s127 : (Eq (Not (Not (Eq (f a b) (f b b)))) (Eq (f a b) (f b b))) := trueElim lean_s126
let lean_s128 := congr lean_s121 lean_s127
have lean_s129 : (Eq (Not (Eq a (f a b))) (Not (Eq a (f a b)))) := rfl
let lean_s130 := congr lean_s121 lean_s129
have lean_s131 : (Eq (Not (Eq a (f b b))) (Not (Eq a (f b b)))) := rfl
let lean_s132 := congr lean_s130 lean_s131
have lean_s133 : (Eq (Or (Not (Not (Eq (f a b) (f b b)))) (Or (Not (Eq a (f a b))) (Not (Eq a (f b b))))) (Or (Eq (f a b) (f b b)) (Or (Not (Eq a (f a b))) (Not (Eq a (f b b)))))) := congr lean_s128 lean_s132
have lean_s134 : (Or (Eq (f a b) (f b b)) (Or (Not (Eq a (f a b))) (Not (Eq a (f b b))))) := eqResolve lean_s120 lean_s133
let lean_s135 := by R1 lean_s115, lean_s134, (Eq a (f b b)), [(- 1), (- 1)]
let lean_s136 := by R1 lean_s135, lean_a57, (Eq (f a b) (f b b)), [(- 1), 0]
have lean_s137 : (Or (And (Not (Eq (f a b) (f c b))) (Eq a (f a b))) (Or (Not (Not (Eq (f a b) (f c b)))) (Not (Eq a (f a b))))) := cnfAndNeg [(Not (Eq (f a b) (f c b))), (Eq a (f a b))]
have lean_s138 : (Or (Not (Not (Eq (f a b) (f c b)))) (Or (Not (Eq a (f a b))) (Not (Eq a (f c b))))) :=
  (scope (fun lean_a70 : (Not (Eq (f a b) (f c b))) =>
    (scope (fun lean_a71 : (Eq a (f a b)) =>
      have lean_s138 : (Eq (f a b) a) := Eq.symm lean_a71
      have lean_s139 : (Eq a (f a b)) := Eq.symm lean_s138
      let lean_s140 := flipCongrArg lean_s139 [Eq]
      have lean_s141 : (Eq (f c b) (f c b)) := rfl
      have lean_s142 : (Eq (Eq a (f c b)) (Eq (f a b) (f c b))) := congr lean_s140 lean_s141
      have lean_s143 : (Eq (Eq (f a b) (f c b)) False) := falseIntro lean_a70
      have lean_s144 : (Eq (Eq a (f c b)) False) := Eq.trans lean_s142 lean_s143
      have lean_s145 : (Not (Eq a (f c b))) := falseElim lean_s144
      show (Not (Eq a (f c b))) from lean_s145
  ))))
have lean_s139 : (Implies (And (Not (Eq (f a b) (f c b))) (Eq a (f a b))) (Not (Eq a (f c b)))) := by liftOrNToImp lean_s138, 2
have lean_s140 : (Or (Not (And (Not (Eq (f a b) (f c b))) (Eq a (f a b)))) (Not (Eq a (f c b)))) := impliesElim lean_s139
have lean_s141 : (Or (Not (Not (Eq (f a b) (f c b)))) (Or (Not (Eq a (f a b))) (Not (Eq a (f c b))))) := by R1 lean_s137, lean_s140, (And (Not (Eq (f a b) (f c b))) (Eq a (f a b))), [(- 1), (- 1)]
have lean_s142 : (Eq Or Or) := rfl
have lean_s143 : (Eq (Eq (f a b) (f c b)) (Eq (f a b) (f c b))) := rfl
let lean_s144 := flipCongrArg lean_s143 [Eq]
have lean_s145 : (Eq (Eq (Eq (f a b) (f c b)) (Not (Not (Eq (f a b) (f c b))))) (Eq (Eq (f a b) (f c b)) (Eq (f a b) (f c b)))) := congr lean_s144 lean_r9
have lean_s146 : (Eq (Eq (Eq (f a b) (f c b)) (Not (Not (Eq (f a b) (f c b))))) True) := Eq.trans lean_s145 lean_r11
have lean_s147 : (Eq (Eq (Not (Not (Eq (f a b) (f c b)))) (Eq (f a b) (f c b))) True) := Eq.trans lean_r12 lean_s146
have lean_s148 : (Eq (Not (Not (Eq (f a b) (f c b)))) (Eq (f a b) (f c b))) := trueElim lean_s147
let lean_s149 := congr lean_s142 lean_s148
let lean_s150 := congr lean_s142 lean_s129
have lean_s151 : (Eq (Not (Eq a (f c b))) (Not (Eq a (f c b)))) := rfl
let lean_s152 := congr lean_s150 lean_s151
have lean_s153 : (Eq (Or (Not (Not (Eq (f a b) (f c b)))) (Or (Not (Eq a (f a b))) (Not (Eq a (f c b))))) (Or (Eq (f a b) (f c b)) (Or (Not (Eq a (f a b))) (Not (Eq a (f c b)))))) := congr lean_s149 lean_s152
have lean_s154 : (Or (Eq (f a b) (f c b)) (Or (Not (Eq a (f a b))) (Not (Eq a (f c b))))) := eqResolve lean_s141 lean_s153
let lean_s155 := by R1 lean_s136, lean_s154, (Eq a (f c b)), [(- 1), (- 1)]
have lean_s156 : (Or (Eq c (f c b)) (Or (Not (Eq a (f a b))) (Not (Eq a (f a b))))) := by R1 lean_s155, lean_a58, (Eq (f a b) (f c b)), [(- 1), 0]
have lean_s157 : (Or (Eq c (f c b)) (Not (Eq a (f a b)))) := by factor lean_s156, (- 1)
have lean_s158 : (Eq Or Or) := rfl
let lean_s159 := congr lean_s158 lean_r16
let lean_s160 := congr lean_s158 lean_r19
let lean_s161 := congr lean_s160 lean_r14
have lean_s162 : (Eq (Or (Eq (f a b) a) (Or (Eq (f b b) b) (Eq (f c b) c))) (Or (Eq a (f a b)) (Or (Eq b (f b b)) (Eq c (f c b))))) := congr lean_s159 lean_s161
have lean_s163 : (Or (Eq a (f a b)) (Or (Eq b (f b b)) (Eq c (f c b)))) := eqResolve lean_a46 lean_s162
let lean_s164 := by R2 lean_s157, lean_s163, (Eq a (f a b)), [(- 1), (- 1)]
have lean_s165 : (Not (Eq b (f b b))) := negSymm lean_a49
have lean_s166 : (Or (Eq c (f c b)) (Eq c (f c b))) := by R1 lean_s164, lean_s165, (Eq b (f b b)), [(- 1), 0]
have lean_s167 : (Eq c (f c b)) := by factor lean_s166, 1
have lean_s168 : (Not (Eq b (f c b))) := by R2 lean_s68, lean_s167, (Eq c (f c b)), [(- 1), 0]
let lean_s169 := by R1 lean_s5, lean_s168, (Eq b (f c b)), [(- 1), 0]
have lean_s170 : (Eq Or Or) := rfl
let lean_s171 := congr lean_s170 lean_r1
let lean_s172 := congr lean_s170 lean_r2
let lean_s173 := congr lean_s172 lean_r3
have lean_s174 : (Eq (Or (Eq (f a a) c) (Or (Eq (f b b) c) (Eq (f c c) c))) (Or (Eq c (f a a)) (Or (Eq c (f b b)) (Eq c (f c c))))) := congr lean_s171 lean_s173
have lean_s175 : (Or (Eq c (f a a)) (Or (Eq c (f b b)) (Eq c (f c c)))) := eqResolve lean_a44 lean_s174
have lean_s176 : (Or (And (Not (Eq (f b b) (f c b))) (Eq c (f b b))) (Or (Not (Not (Eq (f b b) (f c b)))) (Not (Eq c (f b b))))) := cnfAndNeg [(Not (Eq (f b b) (f c b))), (Eq c (f b b))]
have lean_s177 : (Or (Not (Not (Eq (f b b) (f c b)))) (Or (Not (Eq c (f b b))) (Not (Eq c (f c b))))) :=
  (scope (fun lean_a70 : (Not (Eq (f b b) (f c b))) =>
    (scope (fun lean_a71 : (Eq c (f b b)) =>
      have lean_s177 : (Eq (f b b) c) := Eq.symm lean_a71
      have lean_s178 : (Eq c (f b b)) := Eq.symm lean_s177
      let lean_s179 := flipCongrArg lean_s178 [Eq]
      have lean_s180 : (Eq (f c b) (f c b)) := rfl
      have lean_s181 : (Eq (Eq c (f c b)) (Eq (f b b) (f c b))) := congr lean_s179 lean_s180
      have lean_s182 : (Eq (Eq (f b b) (f c b)) False) := falseIntro lean_a70
      have lean_s183 : (Eq (Eq c (f c b)) False) := Eq.trans lean_s181 lean_s182
      have lean_s184 : (Not (Eq c (f c b))) := falseElim lean_s183
      show (Not (Eq c (f c b))) from lean_s184
  ))))
have lean_s178 : (Implies (And (Not (Eq (f b b) (f c b))) (Eq c (f b b))) (Not (Eq c (f c b)))) := by liftOrNToImp lean_s177, 2
have lean_s179 : (Or (Not (And (Not (Eq (f b b) (f c b))) (Eq c (f b b)))) (Not (Eq c (f c b)))) := impliesElim lean_s178
have lean_s180 : (Or (Not (Not (Eq (f b b) (f c b)))) (Or (Not (Eq c (f b b))) (Not (Eq c (f c b))))) := by R1 lean_s176, lean_s179, (And (Not (Eq (f b b) (f c b))) (Eq c (f b b))), [(- 1), (- 1)]
have lean_s181 : (Eq Or Or) := rfl
have lean_s182 : (Eq (Eq (f b b) (f c b)) (Eq (f b b) (f c b))) := rfl
let lean_s183 := flipCongrArg lean_s182 [Eq]
have lean_s184 : (Eq (Eq (Eq (f b b) (f c b)) (Not (Not (Eq (f b b) (f c b))))) (Eq (Eq (f b b) (f c b)) (Eq (f b b) (f c b)))) := congr lean_s183 lean_r8
have lean_s185 : (Eq (Eq (Eq (f b b) (f c b)) (Not (Not (Eq (f b b) (f c b))))) True) := Eq.trans lean_s184 lean_r5
have lean_s186 : (Eq (Eq (Not (Not (Eq (f b b) (f c b)))) (Eq (f b b) (f c b))) True) := Eq.trans lean_r4 lean_s185
have lean_s187 : (Eq (Not (Not (Eq (f b b) (f c b)))) (Eq (f b b) (f c b))) := trueElim lean_s186
let lean_s188 := congr lean_s181 lean_s187
have lean_s189 : (Eq (Not (Eq c (f b b))) (Not (Eq c (f b b)))) := rfl
let lean_s190 := congr lean_s181 lean_s189
let lean_s191 := congr lean_s190 lean_s23
have lean_s192 : (Eq (Or (Not (Not (Eq (f b b) (f c b)))) (Or (Not (Eq c (f b b))) (Not (Eq c (f c b))))) (Or (Eq (f b b) (f c b)) (Or (Not (Eq c (f b b))) (Not (Eq c (f c b)))))) := congr lean_s188 lean_s191
have lean_s193 : (Or (Eq (f b b) (f c b)) (Or (Not (Eq c (f b b))) (Not (Eq c (f c b))))) := eqResolve lean_s180 lean_s192
let lean_s194 := by R1 lean_s193, lean_a59, (Eq (f b b) (f c b)), [(- 1), 0]
have lean_s195 : (Not (Eq c (f b b))) := by R2 lean_s194, lean_s167, (Eq c (f c b)), [(- 1), 0]
let lean_s196 := by R1 lean_s175, lean_s195, (Eq c (f b b)), [(- 1), 0]
have lean_s197 : (Not (Eq c (f c c))) := negSymm lean_a50
have lean_s198 : (Eq c (f a a)) := by R1 lean_s196, lean_s197, (Eq c (f c c)), [(- 1), 0]
let lean_s199 := by R2 lean_s169, lean_s198, (Eq c (f a a)), [(- 1), 0]
let lean_s200 := by R2 lean_s199, lean_s167, (Eq c (f c b)), [(- 1), 0]
exact (show False from by R2 lean_s200, lean_s37, (Eq b (f a a)), [0, 0])
