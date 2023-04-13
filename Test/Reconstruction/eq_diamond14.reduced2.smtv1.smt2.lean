import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {V : Type u} [Nonempty V]
variable {y6 : V}
variable {x6 : V}
variable {z6 : V}
variable {x7 : V}
variable {y7 : V}
variable {y5 : V}
variable {x2 : V}
variable {x5 : V}
variable {z5 : V}
variable {y2 : V}
variable {y6 : V}
variable {x6 : V}
variable {z6 : V}
variable {x9 : V}
variable {x3 : V}
variable {x7 : V}
variable {y7 : V}
variable {x8 : V}
variable {y3 : V}
variable {x8 : V}
variable {y8 : V}
variable {y8 : V}
variable {y10 : V}
variable {x4 : V}
variable {z10 : V}
variable {x0 : V}
variable {z10 : V}
variable {x13 : V}
variable {x5 : V}
variable {x9 : V}
variable {z5 : V}
variable {z9 : V}
variable {x10 : V}
variable {y5 : V}
variable {z12 : V}
variable {x12 : V}
variable {y12 : V}
variable {z11 : V}
variable {y10 : V}
variable {y4 : V}
variable {x11 : V}
variable {y11 : V}
variable {y4 : V}
variable {y1 : V}
variable {x4 : V}
variable {y3 : V}
variable {x13 : V}
variable {x1 : V}
variable {x3 : V}
variable {x0 : V}
variable {y2 : V}
variable {x2 : V}
variable {y0 : V}
variable {z9 : V}
variable {y1 : V}
variable {x10 : V}
variable {x1 : V}
variable {y0 : V}
variable {z12 : V}
variable {x12 : V}
variable {y12 : V}
variable {z11 : V}
variable {x11 : V}
variable {y11 : V}

theorem th0 : (Eq (And (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Not (Eq x13 y0)))))) (And (Implies (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Eq x13 x12)) (And (Implies (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (Eq x12 x11)) (And (Implies (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (Eq x11 x7)) (And (Implies (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (Eq x7 y0)) (And (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Not (Eq x13 y0))))))))))) → (Eq (Eq (Not (Not (Eq x13 y0))) (Eq x13 y0)) (Eq (Eq x13 y0) (Not (Not (Eq x13 y0))))) → (Eq (Not (Not (Eq x13 y0))) (Eq x13 y0)) → (Eq (Eq (Eq x13 y0) (Eq x13 y0)) True) → (Eq (Eq x7 x10) (Eq x10 x7)) → (Eq (Eq y10 x11) (Eq x11 y10)) → (Eq (Eq y11 x12) (Eq x12 y11)) → (Eq (Eq x12 z12) (Eq z12 x12)) → (Eq (Eq x0 x13) (Eq x13 x0)) → (Eq (Eq x6 z6) (Eq z6 x6)) → (Eq (Eq y8 x9) (Eq x9 y8)) → (Eq (Eq y12 x13) (Eq x13 y12)) → (Eq (Eq x7 y10) (Eq y10 x7)) → (Eq (And (And (Eq z5 x5) (Eq x6 z5)) (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (And (Eq z9 x9) (Eq z9 x10)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (Eq x9 y8))))))))))))))))))))) (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10)))))))))))))))))))))))) → (Eq (Eq x7 y7) (Eq y7 x7)) → (Eq (Eq x11 z11) (Eq z11 x11)) → (Eq (Eq y0 y6) (Eq y6 y0)) → (Eq (Eq x4 y4) (Eq y4 x4)) → (Eq (Eq x8 y8) (Eq y8 x8)) → (Eq (Eq y4 x5) (Eq x5 y4)) → (Eq (Eq x10 z9) (Eq z9 x10)) → (Eq (Eq y6 x7) (Eq x7 y6)) → (Eq (And (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 y0)) (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True True)))))))))))))))))))))) (And (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Not (Eq x13 y0))))))) → (Eq (Eq y7 x8) (Eq x8 y7)) → (Eq (Eq x7 z10) (Eq z10 x7)) → (Eq (Or False (And (Eq z5 x5) (Eq x6 z5))) (And (Eq z5 x5) (Eq x6 z5))) → (Eq (Eq y3 x4) (Eq x4 y3)) → (Eq (Eq x3 y3) (Eq y3 x3)) → (Eq (Eq y2 x3) (Eq x3 y2)) → (Eq (Eq x2 y2) (Eq y2 x2)) → (Eq (Eq x5 z5) (Eq z5 x5)) → (Eq (Eq y1 x2) (Eq x2 y1)) → (Eq (And False (Eq y5 x6)) False) → (Eq (Eq x7 x7) True) → (Eq (Eq x1 y1) (Eq y1 x1)) → (Eq (And (And (Eq x0 y0) (Eq y0 x1)) (And (And (Eq x1 y1) (Eq y1 x2)) (And (And (Eq x2 y2) (Eq y2 x3)) (And (And (Eq x3 y3) (Eq y3 x4)) (And (And (Eq x4 y4) (Eq y4 x5)) (And (Or (And False (Eq y5 x6)) (And (Eq x5 z5) (Eq x6 z5))) (And (Or (And (Eq x6 y6) (Eq y6 x7)) (And (Eq x6 z6) (Eq x7 z6))) (And (And (Eq x7 y7) (Eq y7 x8)) (And (And (Eq x8 y8) (Eq y8 x9)) (And (Or (And (Eq x10 y10) (Eq y10 x11)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq y11 x12)) (And (Eq x11 z11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq y12 x13)) (And (Eq x12 z12) (Eq x13 z12))) (And (Not (Eq x0 x13)) (Or False (And (Eq x9 z9) (Eq x10 z9)))))))))))))))) (And (Or (And False (Eq y5 x6)) (And (Eq x5 z5) (Eq x6 z5))) (And (Or (And (Eq x6 y6) (Eq y6 x7)) (And (Eq x6 z6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq y10 x11)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq y11 x12)) (And (Eq x11 z11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq y12 x13)) (And (Eq x12 z12) (Eq x13 z12))) (And (Not (Eq x0 x13)) (And (Or False (And (Eq x9 z9) (Eq x10 z9))) (And (Eq x0 y0) (And (Eq y0 x1) (And (Eq x1 y1) (And (Eq y1 x2) (And (Eq x2 y2) (And (Eq y2 x3) (And (Eq x3 y3) (And (Eq y3 x4) (And (Eq x4 y4) (And (Eq y4 x5) (And (Eq x7 y7) (And (Eq y7 x8) (And (Eq x8 y8) (Eq y8 x9)))))))))))))))))))))) → (Eq (Eq y0 y0) True) → (Eq (Eq y0 x1) (Eq x1 y0)) → (Eq (Eq x9 z9) (Eq z9 x9)) → (Eq (Or False (And (Eq x9 z9) (Eq x10 z9))) (And (Eq x9 z9) (Eq x10 z9))) → (And (And (Eq x0 y0) (Eq y0 x1)) (And (And (Eq x1 y1) (Eq y1 x2)) (And (And (Eq x2 y2) (Eq y2 x3)) (And (And (Eq x3 y3) (Eq y3 x4)) (And (And (Eq x4 y4) (Eq y4 x5)) (And (Or (And False (Eq y5 x6)) (And (Eq x5 z5) (Eq x6 z5))) (And (Or (And (Eq x6 y6) (Eq y6 x7)) (And (Eq x6 z6) (Eq x7 z6))) (And (And (Eq x7 y7) (Eq y7 x8)) (And (And (Eq x8 y8) (Eq y8 x9)) (And (Or (And (Eq x10 y10) (Eq y10 x11)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq y11 x12)) (And (Eq x11 z11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq y12 x13)) (And (Eq x12 z12) (Eq x13 z12))) (And (Not (Eq x0 x13)) (Or False (And (Eq x9 z9) (Eq x10 z9)))))))))))))))) → False :=
fun lean_h0 : (Eq (And (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Not (Eq x13 y0)))))) (And (Implies (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Eq x13 x12)) (And (Implies (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (Eq x12 x11)) (And (Implies (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (Eq x11 x7)) (And (Implies (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (Eq x7 y0)) (And (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Not (Eq x13 y0))))))))))) =>
fun lean_r1 : (Eq (Eq (Not (Not (Eq x13 y0))) (Eq x13 y0)) (Eq (Eq x13 y0) (Not (Not (Eq x13 y0))))) =>
fun lean_r2 : (Eq (Not (Not (Eq x13 y0))) (Eq x13 y0)) =>
fun lean_r3 : (Eq (Eq (Eq x13 y0) (Eq x13 y0)) True) =>
fun lean_r4 : (Eq (Eq x7 x10) (Eq x10 x7)) =>
fun lean_r5 : (Eq (Eq y10 x11) (Eq x11 y10)) =>
fun lean_r6 : (Eq (Eq y11 x12) (Eq x12 y11)) =>
fun lean_r7 : (Eq (Eq x12 z12) (Eq z12 x12)) =>
fun lean_r8 : (Eq (Eq x0 x13) (Eq x13 x0)) =>
fun lean_r9 : (Eq (Eq x6 z6) (Eq z6 x6)) =>
fun lean_r10 : (Eq (Eq y8 x9) (Eq x9 y8)) =>
fun lean_r11 : (Eq (Eq y12 x13) (Eq x13 y12)) =>
fun lean_r12 : (Eq (Eq x7 y10) (Eq y10 x7)) =>
fun lean_r13 : (Eq (And (And (Eq z5 x5) (Eq x6 z5)) (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (And (Eq z9 x9) (Eq z9 x10)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (Eq x9 y8))))))))))))))))))))) (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10)))))))))))))))))))))))) =>
fun lean_r14 : (Eq (Eq x7 y7) (Eq y7 x7)) =>
fun lean_r15 : (Eq (Eq x11 z11) (Eq z11 x11)) =>
fun lean_r16 : (Eq (Eq y0 y6) (Eq y6 y0)) =>
fun lean_r17 : (Eq (Eq x4 y4) (Eq y4 x4)) =>
fun lean_r18 : (Eq (Eq x8 y8) (Eq y8 x8)) =>
fun lean_r19 : (Eq (Eq y4 x5) (Eq x5 y4)) =>
fun lean_r20 : (Eq (Eq x10 z9) (Eq z9 x10)) =>
fun lean_r21 : (Eq (Eq y6 x7) (Eq x7 y6)) =>
fun lean_r22 : (Eq (And (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 y0)) (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True True)))))))))))))))))))))) (And (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Not (Eq x13 y0))))))) =>
fun lean_r23 : (Eq (Eq y7 x8) (Eq x8 y7)) =>
fun lean_r24 : (Eq (Eq x7 z10) (Eq z10 x7)) =>
fun lean_r25 : (Eq (Or False (And (Eq z5 x5) (Eq x6 z5))) (And (Eq z5 x5) (Eq x6 z5))) =>
fun lean_r26 : (Eq (Eq y3 x4) (Eq x4 y3)) =>
fun lean_r27 : (Eq (Eq x3 y3) (Eq y3 x3)) =>
fun lean_r28 : (Eq (Eq y2 x3) (Eq x3 y2)) =>
fun lean_r29 : (Eq (Eq x2 y2) (Eq y2 x2)) =>
fun lean_r30 : (Eq (Eq x5 z5) (Eq z5 x5)) =>
fun lean_r31 : (Eq (Eq y1 x2) (Eq x2 y1)) =>
fun lean_r32 : (Eq (And False (Eq y5 x6)) False) =>
fun lean_r33 : (Eq (Eq x7 x7) True) =>
fun lean_r34 : (Eq (Eq x1 y1) (Eq y1 x1)) =>
fun lean_r35 : (Eq (And (And (Eq x0 y0) (Eq y0 x1)) (And (And (Eq x1 y1) (Eq y1 x2)) (And (And (Eq x2 y2) (Eq y2 x3)) (And (And (Eq x3 y3) (Eq y3 x4)) (And (And (Eq x4 y4) (Eq y4 x5)) (And (Or (And False (Eq y5 x6)) (And (Eq x5 z5) (Eq x6 z5))) (And (Or (And (Eq x6 y6) (Eq y6 x7)) (And (Eq x6 z6) (Eq x7 z6))) (And (And (Eq x7 y7) (Eq y7 x8)) (And (And (Eq x8 y8) (Eq y8 x9)) (And (Or (And (Eq x10 y10) (Eq y10 x11)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq y11 x12)) (And (Eq x11 z11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq y12 x13)) (And (Eq x12 z12) (Eq x13 z12))) (And (Not (Eq x0 x13)) (Or False (And (Eq x9 z9) (Eq x10 z9)))))))))))))))) (And (Or (And False (Eq y5 x6)) (And (Eq x5 z5) (Eq x6 z5))) (And (Or (And (Eq x6 y6) (Eq y6 x7)) (And (Eq x6 z6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq y10 x11)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq y11 x12)) (And (Eq x11 z11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq y12 x13)) (And (Eq x12 z12) (Eq x13 z12))) (And (Not (Eq x0 x13)) (And (Or False (And (Eq x9 z9) (Eq x10 z9))) (And (Eq x0 y0) (And (Eq y0 x1) (And (Eq x1 y1) (And (Eq y1 x2) (And (Eq x2 y2) (And (Eq y2 x3) (And (Eq x3 y3) (And (Eq y3 x4) (And (Eq x4 y4) (And (Eq y4 x5) (And (Eq x7 y7) (And (Eq y7 x8) (And (Eq x8 y8) (Eq y8 x9)))))))))))))))))))))) =>
fun lean_r36 : (Eq (Eq y0 y0) True) =>
fun lean_r37 : (Eq (Eq y0 x1) (Eq x1 y0)) =>
fun lean_r38 : (Eq (Eq x9 z9) (Eq z9 x9)) =>
fun lean_r39 : (Eq (Or False (And (Eq x9 z9) (Eq x10 z9))) (And (Eq x9 z9) (Eq x10 z9))) =>
fun lean_a40 : (And (And (Eq x0 y0) (Eq y0 x1)) (And (And (Eq x1 y1) (Eq y1 x2)) (And (And (Eq x2 y2) (Eq y2 x3)) (And (And (Eq x3 y3) (Eq y3 x4)) (And (And (Eq x4 y4) (Eq y4 x5)) (And (Or (And False (Eq y5 x6)) (And (Eq x5 z5) (Eq x6 z5))) (And (Or (And (Eq x6 y6) (Eq y6 x7)) (And (Eq x6 z6) (Eq x7 z6))) (And (And (Eq x7 y7) (Eq y7 x8)) (And (And (Eq x8 y8) (Eq y8 x9)) (And (Or (And (Eq x10 y10) (Eq y10 x11)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq y11 x12)) (And (Eq x11 z11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq y12 x13)) (And (Eq x12 z12) (Eq x13 z12))) (And (Not (Eq x0 x13)) (Or False (And (Eq x9 z9) (Eq x10 z9)))))))))))))))) => by
have lean_s0 : (Eq And And) := rfl
let lean_s1 := flipCongrArg lean_r32 [Or]
let lean_s2 := flipCongrArg lean_r30 [And]
have lean_s3 : (Eq (Eq x6 z5) (Eq x6 z5)) := rfl
have lean_s4 : (Eq (And (Eq x5 z5) (Eq x6 z5)) (And (Eq z5 x5) (Eq x6 z5))) := congr lean_s2 lean_s3
have lean_s5 : (Eq (Or (And False (Eq y5 x6)) (And (Eq x5 z5) (Eq x6 z5))) (Or False (And (Eq z5 x5) (Eq x6 z5)))) := congr lean_s1 lean_s4
have lean_s6 : (Eq (Or (And False (Eq y5 x6)) (And (Eq x5 z5) (Eq x6 z5))) (And (Eq z5 x5) (Eq x6 z5))) := Eq.trans lean_s5 lean_r25
let lean_s7 := congr lean_s0 lean_s6
have lean_s8 : (Eq (Eq x6 y6) (Eq x6 y6)) := rfl
let lean_s9 := flipCongrArg lean_s8 [And]
have lean_s10 : (Eq (And (Eq x6 y6) (Eq y6 x7)) (And (Eq x6 y6) (Eq x7 y6))) := congr lean_s9 lean_r21
let lean_s11 := flipCongrArg lean_s10 [Or]
let lean_s12 := flipCongrArg lean_r9 [And]
have lean_s13 : (Eq (Eq x7 z6) (Eq x7 z6)) := rfl
have lean_s14 : (Eq (And (Eq x6 z6) (Eq x7 z6)) (And (Eq z6 x6) (Eq x7 z6))) := congr lean_s12 lean_s13
have lean_s15 : (Eq (Or (And (Eq x6 y6) (Eq y6 x7)) (And (Eq x6 z6) (Eq x7 z6))) (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6)))) := congr lean_s11 lean_s14
let lean_s16 := congr lean_s0 lean_s15
have lean_s17 : (Eq (Eq x10 y10) (Eq x10 y10)) := rfl
let lean_s18 := flipCongrArg lean_s17 [And]
have lean_s19 : (Eq (And (Eq x10 y10) (Eq y10 x11)) (And (Eq x10 y10) (Eq x11 y10))) := congr lean_s18 lean_r5
let lean_s20 := flipCongrArg lean_s19 [Or]
have lean_s21 : (Eq (And (Eq x10 z10) (Eq x11 z10)) (And (Eq x10 z10) (Eq x11 z10))) := rfl
have lean_s22 : (Eq (Or (And (Eq x10 y10) (Eq y10 x11)) (And (Eq x10 z10) (Eq x11 z10))) (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10)))) := congr lean_s20 lean_s21
let lean_s23 := congr lean_s0 lean_s22
have lean_s24 : (Eq (Eq x11 y11) (Eq x11 y11)) := rfl
let lean_s25 := flipCongrArg lean_s24 [And]
have lean_s26 : (Eq (And (Eq x11 y11) (Eq y11 x12)) (And (Eq x11 y11) (Eq x12 y11))) := congr lean_s25 lean_r6
let lean_s27 := flipCongrArg lean_s26 [Or]
let lean_s28 := flipCongrArg lean_r15 [And]
have lean_s29 : (Eq (Eq x12 z11) (Eq x12 z11)) := rfl
have lean_s30 : (Eq (And (Eq x11 z11) (Eq x12 z11)) (And (Eq z11 x11) (Eq x12 z11))) := congr lean_s28 lean_s29
have lean_s31 : (Eq (Or (And (Eq x11 y11) (Eq y11 x12)) (And (Eq x11 z11) (Eq x12 z11))) (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11)))) := congr lean_s27 lean_s30
let lean_s32 := congr lean_s0 lean_s31
have lean_s33 : (Eq (Eq x12 y12) (Eq x12 y12)) := rfl
let lean_s34 := flipCongrArg lean_s33 [And]
have lean_s35 : (Eq (And (Eq x12 y12) (Eq y12 x13)) (And (Eq x12 y12) (Eq x13 y12))) := congr lean_s34 lean_r11
let lean_s36 := flipCongrArg lean_s35 [Or]
let lean_s37 := flipCongrArg lean_r7 [And]
have lean_s38 : (Eq (Eq x13 z12) (Eq x13 z12)) := rfl
have lean_s39 : (Eq (And (Eq x12 z12) (Eq x13 z12)) (And (Eq z12 x12) (Eq x13 z12))) := congr lean_s37 lean_s38
have lean_s40 : (Eq (Or (And (Eq x12 y12) (Eq y12 x13)) (And (Eq x12 z12) (Eq x13 z12))) (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12)))) := congr lean_s36 lean_s39
let lean_s41 := congr lean_s0 lean_s40
have lean_s42 : (Eq (Not (Eq x0 x13)) (Not (Eq x13 x0))) := flipCongrArg lean_r8 [Not]
let lean_s43 := congr lean_s0 lean_s42
let lean_s44 := flipCongrArg lean_r38 [And]
have lean_s45 : (Eq (And (Eq x9 z9) (Eq x10 z9)) (And (Eq z9 x9) (Eq z9 x10))) := congr lean_s44 lean_r20
have lean_s46 : (Eq (Or False (And (Eq x9 z9) (Eq x10 z9))) (And (Eq z9 x9) (Eq z9 x10))) := Eq.trans lean_r39 lean_s45
let lean_s47 := congr lean_s0 lean_s46
have lean_s48 : (Eq (Eq x0 y0) (Eq x0 y0)) := rfl
let lean_s49 := congr lean_s0 lean_s48
let lean_s50 := congr lean_s0 lean_r37
let lean_s51 := congr lean_s0 lean_r34
let lean_s52 := congr lean_s0 lean_r31
let lean_s53 := congr lean_s0 lean_r29
let lean_s54 := congr lean_s0 lean_r28
let lean_s55 := congr lean_s0 lean_r27
let lean_s56 := congr lean_s0 lean_r26
let lean_s57 := congr lean_s0 lean_r17
let lean_s58 := congr lean_s0 lean_r19
let lean_s59 := congr lean_s0 lean_r14
let lean_s60 := congr lean_s0 lean_r23
let lean_s61 := congr lean_s0 lean_r18
let lean_s62 := congr lean_s61 lean_r10
let lean_s63 := congr lean_s60 lean_s62
let lean_s64 := congr lean_s59 lean_s63
let lean_s65 := congr lean_s58 lean_s64
let lean_s66 := congr lean_s57 lean_s65
let lean_s67 := congr lean_s56 lean_s66
let lean_s68 := congr lean_s55 lean_s67
let lean_s69 := congr lean_s54 lean_s68
let lean_s70 := congr lean_s53 lean_s69
let lean_s71 := congr lean_s52 lean_s70
let lean_s72 := congr lean_s51 lean_s71
let lean_s73 := congr lean_s50 lean_s72
let lean_s74 := congr lean_s49 lean_s73
let lean_s75 := congr lean_s47 lean_s74
let lean_s76 := congr lean_s43 lean_s75
let lean_s77 := congr lean_s41 lean_s76
let lean_s78 := congr lean_s32 lean_s77
let lean_s79 := congr lean_s23 lean_s78
let lean_s80 := congr lean_s16 lean_s79
have lean_s81 : (Eq (And (Or (And False (Eq y5 x6)) (And (Eq x5 z5) (Eq x6 z5))) (And (Or (And (Eq x6 y6) (Eq y6 x7)) (And (Eq x6 z6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq y10 x11)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq y11 x12)) (And (Eq x11 z11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq y12 x13)) (And (Eq x12 z12) (Eq x13 z12))) (And (Not (Eq x0 x13)) (And (Or False (And (Eq x9 z9) (Eq x10 z9))) (And (Eq x0 y0) (And (Eq y0 x1) (And (Eq x1 y1) (And (Eq y1 x2) (And (Eq x2 y2) (And (Eq y2 x3) (And (Eq x3 y3) (And (Eq y3 x4) (And (Eq x4 y4) (And (Eq y4 x5) (And (Eq x7 y7) (And (Eq y7 x8) (And (Eq x8 y8) (Eq y8 x9))))))))))))))))))))) (And (And (Eq z5 x5) (Eq x6 z5)) (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (And (Eq z9 x9) (Eq z9 x10)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (Eq x9 y8)))))))))))))))))))))) := congr lean_s7 lean_s80
have lean_s82 : (Eq (And (Or (And False (Eq y5 x6)) (And (Eq x5 z5) (Eq x6 z5))) (And (Or (And (Eq x6 y6) (Eq y6 x7)) (And (Eq x6 z6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq y10 x11)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq y11 x12)) (And (Eq x11 z11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq y12 x13)) (And (Eq x12 z12) (Eq x13 z12))) (And (Not (Eq x0 x13)) (And (Or False (And (Eq x9 z9) (Eq x10 z9))) (And (Eq x0 y0) (And (Eq y0 x1) (And (Eq x1 y1) (And (Eq y1 x2) (And (Eq x2 y2) (And (Eq y2 x3) (And (Eq x3 y3) (And (Eq y3 x4) (And (Eq x4 y4) (And (Eq y4 x5) (And (Eq x7 y7) (And (Eq y7 x8) (And (Eq x8 y8) (Eq y8 x9))))))))))))))))))))) (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10)))))))))))))))))))))))) := Eq.trans lean_s81 lean_r13
have lean_s83 : (Eq (And (And (Eq x0 y0) (Eq y0 x1)) (And (And (Eq x1 y1) (Eq y1 x2)) (And (And (Eq x2 y2) (Eq y2 x3)) (And (And (Eq x3 y3) (Eq y3 x4)) (And (And (Eq x4 y4) (Eq y4 x5)) (And (Or (And False (Eq y5 x6)) (And (Eq x5 z5) (Eq x6 z5))) (And (Or (And (Eq x6 y6) (Eq y6 x7)) (And (Eq x6 z6) (Eq x7 z6))) (And (And (Eq x7 y7) (Eq y7 x8)) (And (And (Eq x8 y8) (Eq y8 x9)) (And (Or (And (Eq x10 y10) (Eq y10 x11)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq y11 x12)) (And (Eq x11 z11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq y12 x13)) (And (Eq x12 z12) (Eq x13 z12))) (And (Not (Eq x0 x13)) (Or False (And (Eq x9 z9) (Eq x10 z9)))))))))))))))) (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10)))))))))))))))))))))))) := Eq.trans lean_r35 lean_s82
have lean_s84 : (Eq And And) := rfl
have lean_s85 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s86 : (Eq z9 x10) := by andElim lean_s85, 22
have lean_s87 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s88 : (Eq z9 x9) := by andElim lean_s87, 21
have lean_s89 : (Eq z9 z9) := rfl
let lean_s90 := flipCongrArg lean_s89 [Eq]
have lean_s91 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s92 : (Eq x6 z5) := by andElim lean_s91, 20
have lean_s93 : (Eq x6 x6) := rfl
let lean_s94 := flipCongrArg lean_s93 [Eq]
have lean_s95 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s96 : (Eq z5 x5) := by andElim lean_s95, 19
have lean_s97 : (Eq z5 z5) := rfl
let lean_s98 := flipCongrArg lean_s97 [Eq]
have lean_s99 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s100 : (Eq x9 y8) := by andElim lean_s99, 18
have lean_s101 : (Eq x9 x9) := rfl
let lean_s102 := flipCongrArg lean_s101 [Eq]
have lean_s103 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s104 : (Eq y8 x8) := by andElim lean_s103, 17
have lean_s105 : (Eq y8 y8) := rfl
let lean_s106 := flipCongrArg lean_s105 [Eq]
have lean_s107 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s108 : (Eq x8 y7) := by andElim lean_s107, 16
have lean_s109 : (Eq x8 x8) := rfl
let lean_s110 := flipCongrArg lean_s109 [Eq]
have lean_s111 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s112 : (Eq y7 x7) := by andElim lean_s111, 15
have lean_s113 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s114 : (Eq x5 y4) := by andElim lean_s113, 14
have lean_s115 : (Eq x5 x5) := rfl
let lean_s116 := flipCongrArg lean_s115 [Eq]
have lean_s117 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s118 : (Eq y4 x4) := by andElim lean_s117, 13
have lean_s119 : (Eq y4 y4) := rfl
let lean_s120 := flipCongrArg lean_s119 [Eq]
have lean_s121 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s122 : (Eq x4 y3) := by andElim lean_s121, 12
have lean_s123 : (Eq x4 x4) := rfl
let lean_s124 := flipCongrArg lean_s123 [Eq]
have lean_s125 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s126 : (Eq y3 x3) := by andElim lean_s125, 11
have lean_s127 : (Eq y3 y3) := rfl
let lean_s128 := flipCongrArg lean_s127 [Eq]
have lean_s129 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s130 : (Eq x3 y2) := by andElim lean_s129, 10
have lean_s131 : (Eq x3 x3) := rfl
let lean_s132 := flipCongrArg lean_s131 [Eq]
have lean_s133 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s134 : (Eq y2 x2) := by andElim lean_s133, 9
have lean_s135 : (Eq y2 y2) := rfl
let lean_s136 := flipCongrArg lean_s135 [Eq]
have lean_s137 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s138 : (Eq x2 y1) := by andElim lean_s137, 8
have lean_s139 : (Eq x2 x2) := rfl
let lean_s140 := flipCongrArg lean_s139 [Eq]
have lean_s141 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s142 : (Eq y1 x1) := by andElim lean_s141, 7
have lean_s143 : (Eq y1 y1) := rfl
let lean_s144 := flipCongrArg lean_s143 [Eq]
have lean_s145 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s146 : (Eq x1 y0) := by andElim lean_s145, 6
have lean_s147 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
have lean_s148 : (Eq x0 y0) := by andElim lean_s147, 5
have lean_s149 : (And (Eq x1 y0) (Eq x0 y0)) := And.intro lean_s146 lean_s148
have lean_s150 : (Eq x1 y0) := by andElim lean_s149, 0
have lean_s151 : (Eq (Eq y1 x1) (Eq y1 y0)) := congr lean_s144 lean_s150
have lean_s152 : (Eq y1 y0) := eqResolve lean_s142 lean_s151
let lean_s153 := And.intro lean_s146 lean_s148
have lean_s154 : (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0))) := And.intro lean_s152 lean_s153
have lean_s155 : (Eq y1 y0) := by andElim lean_s154, 0
have lean_s156 : (Eq (Eq x2 y1) (Eq x2 y0)) := congr lean_s140 lean_s155
have lean_s157 : (Eq x2 y0) := eqResolve lean_s138 lean_s156
let lean_s158 := And.intro lean_s146 lean_s148
let lean_s159 := And.intro lean_s152 lean_s158
have lean_s160 : (And (Eq x2 y0) (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0)))) := And.intro lean_s157 lean_s159
have lean_s161 : (Eq x2 y0) := by andElim lean_s160, 0
have lean_s162 : (Eq (Eq y2 x2) (Eq y2 y0)) := congr lean_s136 lean_s161
have lean_s163 : (Eq y2 y0) := eqResolve lean_s134 lean_s162
let lean_s164 := And.intro lean_s146 lean_s148
let lean_s165 := And.intro lean_s152 lean_s164
let lean_s166 := And.intro lean_s157 lean_s165
have lean_s167 : (And (Eq y2 y0) (And (Eq x2 y0) (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0))))) := And.intro lean_s163 lean_s166
have lean_s168 : (Eq y2 y0) := by andElim lean_s167, 0
have lean_s169 : (Eq (Eq x3 y2) (Eq x3 y0)) := congr lean_s132 lean_s168
have lean_s170 : (Eq x3 y0) := eqResolve lean_s130 lean_s169
let lean_s171 := And.intro lean_s146 lean_s148
let lean_s172 := And.intro lean_s152 lean_s171
let lean_s173 := And.intro lean_s157 lean_s172
let lean_s174 := And.intro lean_s163 lean_s173
have lean_s175 : (And (Eq x3 y0) (And (Eq y2 y0) (And (Eq x2 y0) (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0)))))) := And.intro lean_s170 lean_s174
have lean_s176 : (Eq x3 y0) := by andElim lean_s175, 0
have lean_s177 : (Eq (Eq y3 x3) (Eq y3 y0)) := congr lean_s128 lean_s176
have lean_s178 : (Eq y3 y0) := eqResolve lean_s126 lean_s177
let lean_s179 := And.intro lean_s146 lean_s148
let lean_s180 := And.intro lean_s152 lean_s179
let lean_s181 := And.intro lean_s157 lean_s180
let lean_s182 := And.intro lean_s163 lean_s181
let lean_s183 := And.intro lean_s170 lean_s182
have lean_s184 : (And (Eq y3 y0) (And (Eq x3 y0) (And (Eq y2 y0) (And (Eq x2 y0) (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0))))))) := And.intro lean_s178 lean_s183
have lean_s185 : (Eq y3 y0) := by andElim lean_s184, 0
have lean_s186 : (Eq (Eq x4 y3) (Eq x4 y0)) := congr lean_s124 lean_s185
have lean_s187 : (Eq x4 y0) := eqResolve lean_s122 lean_s186
let lean_s188 := And.intro lean_s146 lean_s148
let lean_s189 := And.intro lean_s152 lean_s188
let lean_s190 := And.intro lean_s157 lean_s189
let lean_s191 := And.intro lean_s163 lean_s190
let lean_s192 := And.intro lean_s170 lean_s191
let lean_s193 := And.intro lean_s178 lean_s192
have lean_s194 : (And (Eq x4 y0) (And (Eq y3 y0) (And (Eq x3 y0) (And (Eq y2 y0) (And (Eq x2 y0) (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0)))))))) := And.intro lean_s187 lean_s193
have lean_s195 : (Eq x4 y0) := by andElim lean_s194, 0
have lean_s196 : (Eq (Eq y4 x4) (Eq y4 y0)) := congr lean_s120 lean_s195
have lean_s197 : (Eq y4 y0) := eqResolve lean_s118 lean_s196
let lean_s198 := And.intro lean_s146 lean_s148
let lean_s199 := And.intro lean_s152 lean_s198
let lean_s200 := And.intro lean_s157 lean_s199
let lean_s201 := And.intro lean_s163 lean_s200
let lean_s202 := And.intro lean_s170 lean_s201
let lean_s203 := And.intro lean_s178 lean_s202
let lean_s204 := And.intro lean_s187 lean_s203
have lean_s205 : (And (Eq y4 y0) (And (Eq x4 y0) (And (Eq y3 y0) (And (Eq x3 y0) (And (Eq y2 y0) (And (Eq x2 y0) (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0))))))))) := And.intro lean_s197 lean_s204
have lean_s206 : (Eq y4 y0) := by andElim lean_s205, 0
have lean_s207 : (Eq (Eq x5 y4) (Eq x5 y0)) := congr lean_s116 lean_s206
have lean_s208 : (Eq x5 y0) := eqResolve lean_s114 lean_s207
let lean_s209 := And.intro lean_s146 lean_s148
let lean_s210 := And.intro lean_s152 lean_s209
let lean_s211 := And.intro lean_s157 lean_s210
let lean_s212 := And.intro lean_s163 lean_s211
let lean_s213 := And.intro lean_s170 lean_s212
let lean_s214 := And.intro lean_s178 lean_s213
let lean_s215 := And.intro lean_s187 lean_s214
let lean_s216 := And.intro lean_s197 lean_s215
let lean_s217 := And.intro lean_s208 lean_s216
have lean_s218 : (And (Eq y7 x7) (And (Eq x5 y0) (And (Eq y4 y0) (And (Eq x4 y0) (And (Eq y3 y0) (And (Eq x3 y0) (And (Eq y2 y0) (And (Eq x2 y0) (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0))))))))))) := And.intro lean_s112 lean_s217
have lean_s219 : (Eq y7 x7) := by andElim lean_s218, 0
have lean_s220 : (Eq (Eq x8 y7) (Eq x8 x7)) := congr lean_s110 lean_s219
have lean_s221 : (Eq x8 x7) := eqResolve lean_s108 lean_s220
let lean_s222 := And.intro lean_s146 lean_s148
let lean_s223 := And.intro lean_s152 lean_s222
let lean_s224 := And.intro lean_s157 lean_s223
let lean_s225 := And.intro lean_s163 lean_s224
let lean_s226 := And.intro lean_s170 lean_s225
let lean_s227 := And.intro lean_s178 lean_s226
let lean_s228 := And.intro lean_s187 lean_s227
let lean_s229 := And.intro lean_s197 lean_s228
let lean_s230 := And.intro lean_s208 lean_s229
let lean_s231 := And.intro lean_s112 lean_s230
have lean_s232 : (And (Eq x8 x7) (And (Eq y7 x7) (And (Eq x5 y0) (And (Eq y4 y0) (And (Eq x4 y0) (And (Eq y3 y0) (And (Eq x3 y0) (And (Eq y2 y0) (And (Eq x2 y0) (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0)))))))))))) := And.intro lean_s221 lean_s231
have lean_s233 : (Eq x8 x7) := by andElim lean_s232, 0
have lean_s234 : (Eq (Eq y8 x8) (Eq y8 x7)) := congr lean_s106 lean_s233
have lean_s235 : (Eq y8 x7) := eqResolve lean_s104 lean_s234
let lean_s236 := And.intro lean_s146 lean_s148
let lean_s237 := And.intro lean_s152 lean_s236
let lean_s238 := And.intro lean_s157 lean_s237
let lean_s239 := And.intro lean_s163 lean_s238
let lean_s240 := And.intro lean_s170 lean_s239
let lean_s241 := And.intro lean_s178 lean_s240
let lean_s242 := And.intro lean_s187 lean_s241
let lean_s243 := And.intro lean_s197 lean_s242
let lean_s244 := And.intro lean_s208 lean_s243
let lean_s245 := And.intro lean_s112 lean_s244
let lean_s246 := And.intro lean_s221 lean_s245
have lean_s247 : (And (Eq y8 x7) (And (Eq x8 x7) (And (Eq y7 x7) (And (Eq x5 y0) (And (Eq y4 y0) (And (Eq x4 y0) (And (Eq y3 y0) (And (Eq x3 y0) (And (Eq y2 y0) (And (Eq x2 y0) (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0))))))))))))) := And.intro lean_s235 lean_s246
have lean_s248 : (Eq y8 x7) := by andElim lean_s247, 0
have lean_s249 : (Eq (Eq x9 y8) (Eq x9 x7)) := congr lean_s102 lean_s248
have lean_s250 : (Eq x9 x7) := eqResolve lean_s100 lean_s249
let lean_s251 := And.intro lean_s146 lean_s148
let lean_s252 := And.intro lean_s152 lean_s251
let lean_s253 := And.intro lean_s157 lean_s252
let lean_s254 := And.intro lean_s163 lean_s253
let lean_s255 := And.intro lean_s170 lean_s254
let lean_s256 := And.intro lean_s178 lean_s255
let lean_s257 := And.intro lean_s187 lean_s256
let lean_s258 := And.intro lean_s197 lean_s257
let lean_s259 := And.intro lean_s208 lean_s258
let lean_s260 := And.intro lean_s112 lean_s259
let lean_s261 := And.intro lean_s221 lean_s260
let lean_s262 := And.intro lean_s235 lean_s261
have lean_s263 : (And (Eq x9 x7) (And (Eq y8 x7) (And (Eq x8 x7) (And (Eq y7 x7) (And (Eq x5 y0) (And (Eq y4 y0) (And (Eq x4 y0) (And (Eq y3 y0) (And (Eq x3 y0) (And (Eq y2 y0) (And (Eq x2 y0) (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0)))))))))))))) := And.intro lean_s250 lean_s262
have lean_s264 : (Eq x5 y0) := by andElim lean_s263, 4
have lean_s265 : (Eq (Eq z5 x5) (Eq z5 y0)) := congr lean_s98 lean_s264
have lean_s266 : (Eq z5 y0) := eqResolve lean_s96 lean_s265
let lean_s267 := And.intro lean_s146 lean_s148
let lean_s268 := And.intro lean_s152 lean_s267
let lean_s269 := And.intro lean_s157 lean_s268
let lean_s270 := And.intro lean_s163 lean_s269
let lean_s271 := And.intro lean_s170 lean_s270
let lean_s272 := And.intro lean_s178 lean_s271
let lean_s273 := And.intro lean_s187 lean_s272
let lean_s274 := And.intro lean_s197 lean_s273
let lean_s275 := And.intro lean_s208 lean_s274
let lean_s276 := And.intro lean_s112 lean_s275
let lean_s277 := And.intro lean_s221 lean_s276
let lean_s278 := And.intro lean_s235 lean_s277
let lean_s279 := And.intro lean_s250 lean_s278
have lean_s280 : (And (Eq z5 y0) (And (Eq x9 x7) (And (Eq y8 x7) (And (Eq x8 x7) (And (Eq y7 x7) (And (Eq x5 y0) (And (Eq y4 y0) (And (Eq x4 y0) (And (Eq y3 y0) (And (Eq x3 y0) (And (Eq y2 y0) (And (Eq x2 y0) (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0))))))))))))))) := And.intro lean_s266 lean_s279
have lean_s281 : (Eq z5 y0) := by andElim lean_s280, 0
have lean_s282 : (Eq (Eq x6 z5) (Eq x6 y0)) := congr lean_s94 lean_s281
have lean_s283 : (Eq x6 y0) := eqResolve lean_s92 lean_s282
let lean_s284 := And.intro lean_s146 lean_s148
let lean_s285 := And.intro lean_s152 lean_s284
let lean_s286 := And.intro lean_s157 lean_s285
let lean_s287 := And.intro lean_s163 lean_s286
let lean_s288 := And.intro lean_s170 lean_s287
let lean_s289 := And.intro lean_s178 lean_s288
let lean_s290 := And.intro lean_s187 lean_s289
let lean_s291 := And.intro lean_s197 lean_s290
let lean_s292 := And.intro lean_s208 lean_s291
let lean_s293 := And.intro lean_s112 lean_s292
let lean_s294 := And.intro lean_s221 lean_s293
let lean_s295 := And.intro lean_s235 lean_s294
let lean_s296 := And.intro lean_s250 lean_s295
let lean_s297 := And.intro lean_s266 lean_s296
have lean_s298 : (And (Eq x6 y0) (And (Eq z5 y0) (And (Eq x9 x7) (And (Eq y8 x7) (And (Eq x8 x7) (And (Eq y7 x7) (And (Eq x5 y0) (And (Eq y4 y0) (And (Eq x4 y0) (And (Eq y3 y0) (And (Eq x3 y0) (And (Eq y2 y0) (And (Eq x2 y0) (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0)))))))))))))))) := And.intro lean_s283 lean_s297
have lean_s299 : (Eq x9 x7) := by andElim lean_s298, 2
have lean_s300 : (Eq (Eq z9 x9) (Eq z9 x7)) := congr lean_s90 lean_s299
have lean_s301 : (Eq z9 x7) := eqResolve lean_s88 lean_s300
let lean_s302 := And.intro lean_s146 lean_s148
let lean_s303 := And.intro lean_s152 lean_s302
let lean_s304 := And.intro lean_s157 lean_s303
let lean_s305 := And.intro lean_s163 lean_s304
let lean_s306 := And.intro lean_s170 lean_s305
let lean_s307 := And.intro lean_s178 lean_s306
let lean_s308 := And.intro lean_s187 lean_s307
let lean_s309 := And.intro lean_s197 lean_s308
let lean_s310 := And.intro lean_s208 lean_s309
let lean_s311 := And.intro lean_s112 lean_s310
let lean_s312 := And.intro lean_s221 lean_s311
let lean_s313 := And.intro lean_s235 lean_s312
let lean_s314 := And.intro lean_s250 lean_s313
let lean_s315 := And.intro lean_s266 lean_s314
let lean_s316 := And.intro lean_s283 lean_s315
have lean_s317 : (And (Eq z9 x7) (And (Eq x6 y0) (And (Eq z5 y0) (And (Eq x9 x7) (And (Eq y8 x7) (And (Eq x8 x7) (And (Eq y7 x7) (And (Eq x5 y0) (And (Eq y4 y0) (And (Eq x4 y0) (And (Eq y3 y0) (And (Eq x3 y0) (And (Eq y2 y0) (And (Eq x2 y0) (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0))))))))))))))))) := And.intro lean_s301 lean_s316
have lean_s318 : (Eq z9 x7) := by andElim lean_s317, 0
let lean_s319 := flipCongrArg lean_s318 [Eq]
have lean_s320 : (Eq x10 x10) := rfl
have lean_s321 : (Eq (Eq z9 x10) (Eq x7 x10)) := congr lean_s319 lean_s320
have lean_s322 : (Eq (Eq z9 x10) (Eq x10 x7)) := Eq.trans lean_s321 lean_r4
have lean_s323 : (Eq x10 x7) := eqResolve lean_s86 lean_s322
let lean_s324 := And.intro lean_s146 lean_s148
let lean_s325 := And.intro lean_s152 lean_s324
let lean_s326 := And.intro lean_s157 lean_s325
let lean_s327 := And.intro lean_s163 lean_s326
let lean_s328 := And.intro lean_s170 lean_s327
let lean_s329 := And.intro lean_s178 lean_s328
let lean_s330 := And.intro lean_s187 lean_s329
let lean_s331 := And.intro lean_s197 lean_s330
let lean_s332 := And.intro lean_s208 lean_s331
let lean_s333 := And.intro lean_s112 lean_s332
let lean_s334 := And.intro lean_s221 lean_s333
let lean_s335 := And.intro lean_s235 lean_s334
let lean_s336 := And.intro lean_s250 lean_s335
let lean_s337 := And.intro lean_s266 lean_s336
let lean_s338 := And.intro lean_s283 lean_s337
let lean_s339 := And.intro lean_s301 lean_s338
have lean_s340 : (And (Eq x10 x7) (And (Eq z9 x7) (And (Eq x6 y0) (And (Eq z5 y0) (And (Eq x9 x7) (And (Eq y8 x7) (And (Eq x8 x7) (And (Eq y7 x7) (And (Eq x5 y0) (And (Eq y4 y0) (And (Eq x4 y0) (And (Eq y3 y0) (And (Eq x3 y0) (And (Eq y2 y0) (And (Eq x2 y0) (And (Eq y1 y0) (And (Eq x1 y0) (Eq x0 y0)))))))))))))))))) := And.intro lean_s323 lean_s339
have lean_s341 : (Eq x6 y0) := by andElim lean_s340, 2
let lean_s342 := flipCongrArg lean_s341 [Eq]
have lean_s343 : (Eq y6 y6) := rfl
have lean_s344 : (Eq (Eq x6 y6) (Eq y0 y6)) := congr lean_s342 lean_s343
let lean_s345 := flipCongrArg lean_s344 [And]
have lean_s346 : (Eq (Eq x7 y6) (Eq x7 y6)) := rfl
have lean_s347 : (Eq (And (Eq x6 y6) (Eq x7 y6)) (And (Eq y0 y6) (Eq x7 y6))) := congr lean_s345 lean_s346
let lean_s348 := flipCongrArg lean_s347 [Or]
have lean_s349 : (Eq z6 z6) := rfl
let lean_s350 := flipCongrArg lean_s349 [Eq]
have lean_s351 : (Eq (Eq z6 x6) (Eq z6 y0)) := congr lean_s350 lean_s341
let lean_s352 := flipCongrArg lean_s351 [And]
have lean_s353 : (Eq (Eq x7 z6) (Eq x7 z6)) := rfl
have lean_s354 : (Eq (And (Eq z6 x6) (Eq x7 z6)) (And (Eq z6 y0) (Eq x7 z6))) := congr lean_s352 lean_s353
have lean_s355 : (Eq (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (Or (And (Eq y0 y6) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6)))) := congr lean_s348 lean_s354
let lean_s356 := congr lean_s84 lean_s355
have lean_s357 : (Eq x10 x7) := by andElim lean_s340, 0
let lean_s358 := flipCongrArg lean_s357 [Eq]
have lean_s359 : (Eq y10 y10) := rfl
have lean_s360 : (Eq (Eq x10 y10) (Eq x7 y10)) := congr lean_s358 lean_s359
let lean_s361 := flipCongrArg lean_s360 [And]
have lean_s362 : (Eq (Eq x11 y10) (Eq x11 y10)) := rfl
have lean_s363 : (Eq (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x7 y10) (Eq x11 y10))) := congr lean_s361 lean_s362
let lean_s364 := flipCongrArg lean_s363 [Or]
let lean_s365 := flipCongrArg lean_s357 [Eq]
have lean_s366 : (Eq z10 z10) := rfl
have lean_s367 : (Eq (Eq x10 z10) (Eq x7 z10)) := congr lean_s365 lean_s366
let lean_s368 := flipCongrArg lean_s367 [And]
have lean_s369 : (Eq (Eq x11 z10) (Eq x11 z10)) := rfl
have lean_s370 : (Eq (And (Eq x10 z10) (Eq x11 z10)) (And (Eq x7 z10) (Eq x11 z10))) := congr lean_s368 lean_s369
have lean_s371 : (Eq (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (Or (And (Eq x7 y10) (Eq x11 y10)) (And (Eq x7 z10) (Eq x11 z10)))) := congr lean_s364 lean_s370
let lean_s372 := congr lean_s84 lean_s371
have lean_s373 : (Eq (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11)))) := rfl
let lean_s374 := congr lean_s84 lean_s373
have lean_s375 : (Eq (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12)))) := rfl
let lean_s376 := congr lean_s84 lean_s375
have lean_s377 : (Eq x13 x13) := rfl
let lean_s378 := flipCongrArg lean_s377 [Eq]
have lean_s379 : (Eq x0 y0) := by andElim lean_s340, 17
have lean_s380 : (Eq (Eq x13 x0) (Eq x13 y0)) := congr lean_s378 lean_s379
have lean_s381 : (Eq (Not (Eq x13 x0)) (Not (Eq x13 y0))) := flipCongrArg lean_s380 [Not]
let lean_s382 := congr lean_s84 lean_s381
let lean_s383 := flipCongrArg lean_s379 [Eq]
have lean_s384 : (Eq y0 y0) := rfl
have lean_s385 : (Eq (Eq x0 y0) (Eq y0 y0)) := congr lean_s383 lean_s384
let lean_s386 := congr lean_s84 lean_s385
have lean_s387 : (Eq x1 y0) := by andElim lean_s340, 16
let lean_s388 := flipCongrArg lean_s387 [Eq]
have lean_s389 : (Eq (Eq x1 y0) (Eq y0 y0)) := congr lean_s388 lean_s384
let lean_s390 := congr lean_s84 lean_s389
have lean_s391 : (Eq y1 y0) := by andElim lean_s340, 15
let lean_s392 := flipCongrArg lean_s391 [Eq]
have lean_s393 : (Eq (Eq y1 x1) (Eq y0 y0)) := congr lean_s392 lean_s387
let lean_s394 := congr lean_s84 lean_s393
have lean_s395 : (Eq x2 y0) := by andElim lean_s340, 14
let lean_s396 := flipCongrArg lean_s395 [Eq]
have lean_s397 : (Eq (Eq x2 y1) (Eq y0 y0)) := congr lean_s396 lean_s391
let lean_s398 := congr lean_s84 lean_s397
have lean_s399 : (Eq y2 y0) := by andElim lean_s340, 13
let lean_s400 := flipCongrArg lean_s399 [Eq]
have lean_s401 : (Eq (Eq y2 x2) (Eq y0 y0)) := congr lean_s400 lean_s395
let lean_s402 := congr lean_s84 lean_s401
have lean_s403 : (Eq x3 y0) := by andElim lean_s340, 12
let lean_s404 := flipCongrArg lean_s403 [Eq]
have lean_s405 : (Eq (Eq x3 y2) (Eq y0 y0)) := congr lean_s404 lean_s399
let lean_s406 := congr lean_s84 lean_s405
have lean_s407 : (Eq y3 y0) := by andElim lean_s340, 11
let lean_s408 := flipCongrArg lean_s407 [Eq]
have lean_s409 : (Eq (Eq y3 x3) (Eq y0 y0)) := congr lean_s408 lean_s403
let lean_s410 := congr lean_s84 lean_s409
have lean_s411 : (Eq x4 y0) := by andElim lean_s340, 10
let lean_s412 := flipCongrArg lean_s411 [Eq]
have lean_s413 : (Eq (Eq x4 y3) (Eq y0 y0)) := congr lean_s412 lean_s407
let lean_s414 := congr lean_s84 lean_s413
have lean_s415 : (Eq y4 y0) := by andElim lean_s340, 9
let lean_s416 := flipCongrArg lean_s415 [Eq]
have lean_s417 : (Eq (Eq y4 x4) (Eq y0 y0)) := congr lean_s416 lean_s411
let lean_s418 := congr lean_s84 lean_s417
have lean_s419 : (Eq x5 y0) := by andElim lean_s340, 8
let lean_s420 := flipCongrArg lean_s419 [Eq]
have lean_s421 : (Eq (Eq x5 y4) (Eq y0 y0)) := congr lean_s420 lean_s415
let lean_s422 := congr lean_s84 lean_s421
have lean_s423 : (Eq y7 x7) := by andElim lean_s340, 7
let lean_s424 := flipCongrArg lean_s423 [Eq]
have lean_s425 : (Eq x7 x7) := rfl
have lean_s426 : (Eq (Eq y7 x7) (Eq x7 x7)) := congr lean_s424 lean_s425
let lean_s427 := congr lean_s84 lean_s426
have lean_s428 : (Eq x8 x7) := by andElim lean_s340, 6
let lean_s429 := flipCongrArg lean_s428 [Eq]
have lean_s430 : (Eq (Eq x8 y7) (Eq x7 x7)) := congr lean_s429 lean_s423
let lean_s431 := congr lean_s84 lean_s430
have lean_s432 : (Eq y8 x7) := by andElim lean_s340, 5
let lean_s433 := flipCongrArg lean_s432 [Eq]
have lean_s434 : (Eq (Eq y8 x8) (Eq x7 x7)) := congr lean_s433 lean_s428
let lean_s435 := congr lean_s84 lean_s434
have lean_s436 : (Eq x9 x7) := by andElim lean_s340, 4
let lean_s437 := flipCongrArg lean_s436 [Eq]
have lean_s438 : (Eq (Eq x9 y8) (Eq x7 x7)) := congr lean_s437 lean_s432
let lean_s439 := congr lean_s84 lean_s438
have lean_s440 : (Eq z5 y0) := by andElim lean_s340, 3
let lean_s441 := flipCongrArg lean_s440 [Eq]
have lean_s442 : (Eq (Eq z5 x5) (Eq y0 y0)) := congr lean_s441 lean_s419
let lean_s443 := congr lean_s84 lean_s442
let lean_s444 := flipCongrArg lean_s341 [Eq]
have lean_s445 : (Eq (Eq x6 z5) (Eq y0 y0)) := congr lean_s444 lean_s440
let lean_s446 := congr lean_s84 lean_s445
have lean_s447 : (Eq z9 x7) := by andElim lean_s340, 1
let lean_s448 := flipCongrArg lean_s447 [Eq]
have lean_s449 : (Eq (Eq z9 x9) (Eq x7 x7)) := congr lean_s448 lean_s436
let lean_s450 := congr lean_s84 lean_s449
let lean_s451 := flipCongrArg lean_s447 [Eq]
have lean_s452 : (Eq (Eq z9 x10) (Eq x7 x7)) := congr lean_s451 lean_s357
let lean_s453 := congr lean_s450 lean_s452
let lean_s454 := congr lean_s446 lean_s453
let lean_s455 := congr lean_s443 lean_s454
let lean_s456 := congr lean_s439 lean_s455
let lean_s457 := congr lean_s435 lean_s456
let lean_s458 := congr lean_s431 lean_s457
let lean_s459 := congr lean_s427 lean_s458
let lean_s460 := congr lean_s422 lean_s459
let lean_s461 := congr lean_s418 lean_s460
let lean_s462 := congr lean_s414 lean_s461
let lean_s463 := congr lean_s410 lean_s462
let lean_s464 := congr lean_s406 lean_s463
let lean_s465 := congr lean_s402 lean_s464
let lean_s466 := congr lean_s398 lean_s465
let lean_s467 := congr lean_s394 lean_s466
let lean_s468 := congr lean_s390 lean_s467
let lean_s469 := congr lean_s386 lean_s468
let lean_s470 := congr lean_s382 lean_s469
let lean_s471 := congr lean_s376 lean_s470
let lean_s472 := congr lean_s374 lean_s471
let lean_s473 := congr lean_s372 lean_s472
have lean_s474 : (Eq (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) (And (Or (And (Eq y0 y6) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq x7 y10) (Eq x11 y10)) (And (Eq x7 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 y0)) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq x7 x7) (And (Eq x7 x7) (And (Eq x7 x7) (And (Eq x7 x7) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq x7 x7) (Eq x7 x7)))))))))))))))))))))))) := congr lean_s356 lean_s473
have lean_s475 : (Eq And And) := rfl
let lean_s476 := flipCongrArg lean_r16 [And]
have lean_s477 : (Eq (Eq x7 y6) (Eq x7 y6)) := rfl
have lean_s478 : (Eq (And (Eq y0 y6) (Eq x7 y6)) (And (Eq y6 y0) (Eq x7 y6))) := congr lean_s476 lean_s477
let lean_s479 := flipCongrArg lean_s478 [Or]
have lean_s480 : (Eq (And (Eq z6 y0) (Eq x7 z6)) (And (Eq z6 y0) (Eq x7 z6))) := rfl
have lean_s481 : (Eq (Or (And (Eq y0 y6) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6)))) := congr lean_s479 lean_s480
let lean_s482 := congr lean_s475 lean_s481
let lean_s483 := flipCongrArg lean_r12 [And]
have lean_s484 : (Eq (Eq x11 y10) (Eq x11 y10)) := rfl
have lean_s485 : (Eq (And (Eq x7 y10) (Eq x11 y10)) (And (Eq y10 x7) (Eq x11 y10))) := congr lean_s483 lean_s484
let lean_s486 := flipCongrArg lean_s485 [Or]
let lean_s487 := flipCongrArg lean_r24 [And]
have lean_s488 : (Eq (Eq x11 z10) (Eq x11 z10)) := rfl
have lean_s489 : (Eq (And (Eq x7 z10) (Eq x11 z10)) (And (Eq z10 x7) (Eq x11 z10))) := congr lean_s487 lean_s488
have lean_s490 : (Eq (Or (And (Eq x7 y10) (Eq x11 y10)) (And (Eq x7 z10) (Eq x11 z10))) (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10)))) := congr lean_s486 lean_s489
let lean_s491 := congr lean_s475 lean_s490
have lean_s492 : (Eq (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11)))) := rfl
let lean_s493 := congr lean_s475 lean_s492
have lean_s494 : (Eq (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12)))) := rfl
let lean_s495 := congr lean_s475 lean_s494
have lean_s496 : (Eq (Not (Eq x13 y0)) (Not (Eq x13 y0))) := rfl
let lean_s497 := congr lean_s475 lean_s496
let lean_s498 := congr lean_s475 lean_r36
let lean_s499 := congr lean_s475 lean_r36
let lean_s500 := congr lean_s475 lean_r36
let lean_s501 := congr lean_s475 lean_r36
let lean_s502 := congr lean_s475 lean_r36
let lean_s503 := congr lean_s475 lean_r36
let lean_s504 := congr lean_s475 lean_r36
let lean_s505 := congr lean_s475 lean_r36
let lean_s506 := congr lean_s475 lean_r36
let lean_s507 := congr lean_s475 lean_r36
let lean_s508 := congr lean_s475 lean_r33
let lean_s509 := congr lean_s475 lean_r33
let lean_s510 := congr lean_s475 lean_r33
let lean_s511 := congr lean_s475 lean_r33
let lean_s512 := congr lean_s475 lean_r36
let lean_s513 := congr lean_s475 lean_r36
let lean_s514 := congr lean_s475 lean_r33
let lean_s515 := congr lean_s514 lean_r33
let lean_s516 := congr lean_s513 lean_s515
let lean_s517 := congr lean_s512 lean_s516
let lean_s518 := congr lean_s511 lean_s517
let lean_s519 := congr lean_s510 lean_s518
let lean_s520 := congr lean_s509 lean_s519
let lean_s521 := congr lean_s508 lean_s520
let lean_s522 := congr lean_s507 lean_s521
let lean_s523 := congr lean_s506 lean_s522
let lean_s524 := congr lean_s505 lean_s523
let lean_s525 := congr lean_s504 lean_s524
let lean_s526 := congr lean_s503 lean_s525
let lean_s527 := congr lean_s502 lean_s526
let lean_s528 := congr lean_s501 lean_s527
let lean_s529 := congr lean_s500 lean_s528
let lean_s530 := congr lean_s499 lean_s529
let lean_s531 := congr lean_s498 lean_s530
let lean_s532 := congr lean_s497 lean_s531
let lean_s533 := congr lean_s495 lean_s532
let lean_s534 := congr lean_s493 lean_s533
let lean_s535 := congr lean_s491 lean_s534
have lean_s536 : (Eq (And (Or (And (Eq y0 y6) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq x7 y10) (Eq x11 y10)) (And (Eq x7 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 y0)) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq x7 x7) (And (Eq x7 x7) (And (Eq x7 x7) (And (Eq x7 x7) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq x7 x7) (Eq x7 x7))))))))))))))))))))))) (And (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 y0)) (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True (And True True))))))))))))))))))))))) := congr lean_s482 lean_s535
have lean_s537 : (Eq (And (Or (And (Eq y0 y6) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq x7 y10) (Eq x11 y10)) (And (Eq x7 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 y0)) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq x7 x7) (And (Eq x7 x7) (And (Eq x7 x7) (And (Eq x7 x7) (And (Eq y0 y0) (And (Eq y0 y0) (And (Eq x7 x7) (Eq x7 x7))))))))))))))))))))))) (And (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Not (Eq x13 y0))))))) := Eq.trans lean_s536 lean_r22
have lean_s538 : (Eq (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) (And (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Not (Eq x13 y0))))))) := Eq.trans lean_s474 lean_s537
let lean_s539 := Eq.trans lean_s83 lean_s538
have lean_s540 : (Eq (And (And (Eq x0 y0) (Eq y0 x1)) (And (And (Eq x1 y1) (Eq y1 x2)) (And (And (Eq x2 y2) (Eq y2 x3)) (And (And (Eq x3 y3) (Eq y3 x4)) (And (And (Eq x4 y4) (Eq y4 x5)) (And (Or (And False (Eq y5 x6)) (And (Eq x5 z5) (Eq x6 z5))) (And (Or (And (Eq x6 y6) (Eq y6 x7)) (And (Eq x6 z6) (Eq x7 z6))) (And (And (Eq x7 y7) (Eq y7 x8)) (And (And (Eq x8 y8) (Eq y8 x9)) (And (Or (And (Eq x10 y10) (Eq y10 x11)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq y11 x12)) (And (Eq x11 z11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq y12 x13)) (And (Eq x12 z12) (Eq x13 z12))) (And (Not (Eq x0 x13)) (Or False (And (Eq x9 z9) (Eq x10 z9)))))))))))))))) (And (Implies (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Eq x13 x12)) (And (Implies (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (Eq x12 x11)) (And (Implies (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (Eq x11 x7)) (And (Implies (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (Eq x7 y0)) (And (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Not (Eq x13 y0))))))))))) := Eq.trans lean_s539 lean_h0
have lean_s541 : (And (Implies (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Eq x13 x12)) (And (Implies (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (Eq x12 x11)) (And (Implies (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (Eq x11 x7)) (And (Implies (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (Eq x7 y0)) (And (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (And (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Not (Eq x13 y0)))))))))) := eqResolve lean_a40 lean_s540
have lean_s542 : (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) := by andElim lean_s541, 7
have lean_s543 : (Or (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Not (And (Eq z12 x12) (Eq x13 z12)))) := @cnfOrNeg [(And (Eq x12 y12) (Eq x13 y12)), (And (Eq z12 x12) (Eq x13 z12))] 1
have lean_s544 : (Implies (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Eq x13 x12)) := by andElim lean_s541, 0
have lean_s545 : (Or (Not (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12)))) (Eq x13 x12)) := impliesElim lean_s544
have lean_s546 : (Or (Eq x13 x12) (Not (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))))) := by permutateOr lean_s545, [1, 0], (- 1)
have lean_s547 : (Or (And (Not (Eq x13 y0)) (And (Eq x7 y0) (And (Eq x11 x7) (Eq x12 x11)))) (Or (Not (Not (Eq x13 y0))) (Or (Not (Eq x7 y0)) (Or (Not (Eq x11 x7)) (Not (Eq x12 x11)))))) := cnfAndNeg [(Not (Eq x13 y0)), (Eq x7 y0), (Eq x11 x7), (Eq x12 x11)]
have lean_s548 : (Or (Not (Not (Eq x13 y0))) (Or (Not (Eq x7 y0)) (Or (Not (Eq x11 x7)) (Or (Not (Eq x12 x11)) (Not (Eq x13 x12)))))) :=
  (scope (fun lean_a41 : (Not (Eq x13 y0)) =>
    (scope (fun lean_a42 : (Eq x7 y0) =>
      (scope (fun lean_a43 : (Eq x11 x7) =>
        (scope (fun lean_a44 : (Eq x12 x11) =>
          have lean_s548 : (Eq x13 x13) := rfl
          let lean_s549 := flipCongrArg lean_s548 [Eq]
          have lean_s550 : (Eq x11 x12) := Eq.symm lean_a44
          have lean_s551 : (Eq x12 x11) := Eq.symm lean_s550
          have lean_s552 : (Eq x7 x11) := Eq.symm lean_a43
          have lean_s553 : (Eq x11 x7) := Eq.symm lean_s552
          let lean_s554 := Eq.trans lean_s551 lean_s553
          have lean_s555 : (Eq y0 x7) := Eq.symm lean_a42
          have lean_s556 : (Eq x7 y0) := Eq.symm lean_s555
          have lean_s557 : (Eq x12 y0) := Eq.trans lean_s554 lean_s556
          have lean_s558 : (Eq (Eq x13 x12) (Eq x13 y0)) := congr lean_s549 lean_s557
          have lean_s559 : (And (Or (And (Eq x6 y6) (Eq x7 y6)) (And (Eq z6 x6) (Eq x7 z6))) (And (Or (And (Eq x10 y10) (Eq x11 y10)) (And (Eq x10 z10) (Eq x11 z10))) (And (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (And (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (And (Not (Eq x13 x0)) (And (Eq x0 y0) (And (Eq x1 y0) (And (Eq y1 x1) (And (Eq x2 y1) (And (Eq y2 x2) (And (Eq x3 y2) (And (Eq y3 x3) (And (Eq x4 y3) (And (Eq y4 x4) (And (Eq x5 y4) (And (Eq y7 x7) (And (Eq x8 y7) (And (Eq y8 x8) (And (Eq x9 y8) (And (Eq z5 x5) (And (Eq x6 z5) (And (Eq z9 x9) (Eq z9 x10))))))))))))))))))))))) := eqResolve lean_a40 lean_s83
          have lean_s560 : (Not (Eq x13 x0)) := by andElim lean_s559, 4
          have lean_s561 : (Eq x13 x13) := rfl
          let lean_s562 := flipCongrArg lean_s561 [Eq]
          have lean_s563 : (Eq x0 y0) := by andElim lean_s340, 17
          have lean_s564 : (Eq (Eq x13 x0) (Eq x13 y0)) := congr lean_s562 lean_s563
          have lean_s565 : (Eq (Not (Eq x13 x0)) (Not (Eq x13 y0))) := flipCongrArg lean_s564 [Not]
          have lean_s566 : (Not (Eq x13 y0)) := eqResolve lean_s560 lean_s565
          have lean_s567 : (Eq (Eq x13 y0) False) := falseIntro lean_s566
          have lean_s568 : (Eq (Eq x13 x12) False) := Eq.trans lean_s558 lean_s567
          have lean_s569 : (Not (Eq x13 x12)) := falseElim lean_s568
          show (Not (Eq x13 x12)) from lean_s569
  ))))))))
have lean_s549 : (Implies (And (Not (Eq x13 y0)) (And (Eq x7 y0) (And (Eq x11 x7) (Eq x12 x11)))) (Not (Eq x13 x12))) := by liftOrNToImp lean_s548, 4
have lean_s550 : (Or (Not (And (Not (Eq x13 y0)) (And (Eq x7 y0) (And (Eq x11 x7) (Eq x12 x11))))) (Not (Eq x13 x12))) := impliesElim lean_s549
have lean_s551 : (Or (Not (Not (Eq x13 y0))) (Or (Not (Eq x7 y0)) (Or (Not (Eq x11 x7)) (Or (Not (Eq x12 x11)) (Not (Eq x13 x12)))))) := by R1 lean_s547, lean_s550, (And (Not (Eq x13 y0)) (And (Eq x7 y0) (And (Eq x11 x7) (Eq x12 x11)))), [(- 1), (- 1)]
have lean_s552 : (Eq Or Or) := rfl
have lean_s553 : (Eq (Eq x13 y0) (Eq x13 y0)) := rfl
let lean_s554 := flipCongrArg lean_s553 [Eq]
have lean_s555 : (Eq (Eq (Eq x13 y0) (Not (Not (Eq x13 y0)))) (Eq (Eq x13 y0) (Eq x13 y0))) := congr lean_s554 lean_r2
have lean_s556 : (Eq (Eq (Eq x13 y0) (Not (Not (Eq x13 y0)))) True) := Eq.trans lean_s555 lean_r3
have lean_s557 : (Eq (Eq (Not (Not (Eq x13 y0))) (Eq x13 y0)) True) := Eq.trans lean_r1 lean_s556
have lean_s558 : (Eq (Not (Not (Eq x13 y0))) (Eq x13 y0)) := trueElim lean_s557
let lean_s559 := congr lean_s552 lean_s558
have lean_s560 : (Eq (Not (Eq x7 y0)) (Not (Eq x7 y0))) := rfl
let lean_s561 := congr lean_s552 lean_s560
have lean_s562 : (Eq (Not (Eq x11 x7)) (Not (Eq x11 x7))) := rfl
let lean_s563 := congr lean_s552 lean_s562
have lean_s564 : (Eq (Not (Eq x12 x11)) (Not (Eq x12 x11))) := rfl
let lean_s565 := congr lean_s552 lean_s564
have lean_s566 : (Eq (Not (Eq x13 x12)) (Not (Eq x13 x12))) := rfl
let lean_s567 := congr lean_s565 lean_s566
let lean_s568 := congr lean_s563 lean_s567
let lean_s569 := congr lean_s561 lean_s568
have lean_s570 : (Eq (Or (Not (Not (Eq x13 y0))) (Or (Not (Eq x7 y0)) (Or (Not (Eq x11 x7)) (Or (Not (Eq x12 x11)) (Not (Eq x13 x12)))))) (Or (Eq x13 y0) (Or (Not (Eq x7 y0)) (Or (Not (Eq x11 x7)) (Or (Not (Eq x12 x11)) (Not (Eq x13 x12))))))) := congr lean_s559 lean_s569
have lean_s571 : (Or (Eq x13 y0) (Or (Not (Eq x7 y0)) (Or (Not (Eq x11 x7)) (Or (Not (Eq x12 x11)) (Not (Eq x13 x12)))))) := eqResolve lean_s551 lean_s570
have lean_s572 : (Or (Eq x13 y0) (Or (Not (Eq x13 x12)) (Or (Not (Eq x12 x11)) (Or (Not (Eq x11 x7)) (Not (Eq x7 y0)))))) := by permutateOr lean_s571, [0, 4, 3, 2, 1], (- 1)
have lean_s573 : (Not (Eq x13 y0)) := by andElim lean_s541, 8
let lean_s574 := by R1 lean_s572, lean_s573, (Eq x13 y0), [(- 1), 0]
have lean_s575 : (Implies (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) (Eq x12 x11)) := by andElim lean_s541, 1
have lean_s576 : (Or (Not (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11)))) (Eq x12 x11)) := impliesElim lean_s575
have lean_s577 : (Or (Eq x12 x11) (Not (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))))) := by permutateOr lean_s576, [1, 0], (- 1)
have lean_s578 : (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))) := by andElim lean_s541, 6
have lean_s579 : (Eq x12 x11) := by R2 lean_s577, lean_s578, (Or (And (Eq x11 y11) (Eq x12 y11)) (And (Eq z11 x11) (Eq x12 z11))), [(- 1), 0]
let lean_s580 := by R2 lean_s574, lean_s579, (Eq x12 x11), [(- 1), 0]
have lean_s581 : (Implies (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) (Eq x11 x7)) := by andElim lean_s541, 2
have lean_s582 : (Or (Not (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10)))) (Eq x11 x7)) := impliesElim lean_s581
have lean_s583 : (Or (Eq x11 x7) (Not (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))))) := by permutateOr lean_s582, [1, 0], (- 1)
have lean_s584 : (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))) := by andElim lean_s541, 5
have lean_s585 : (Eq x11 x7) := by R2 lean_s583, lean_s584, (Or (And (Eq y10 x7) (Eq x11 y10)) (And (Eq z10 x7) (Eq x11 z10))), [(- 1), 0]
let lean_s586 := by R2 lean_s580, lean_s585, (Eq x11 x7), [(- 1), 0]
have lean_s587 : (Implies (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (Eq x7 y0)) := by andElim lean_s541, 3
have lean_s588 : (Or (Not (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6)))) (Eq x7 y0)) := impliesElim lean_s587
have lean_s589 : (Or (Eq x7 y0) (Not (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))))) := by permutateOr lean_s588, [1, 0], (- 1)
have lean_s590 : (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) := by andElim lean_s541, 4
have lean_s591 : (Or (And (Eq z6 y0) (Eq x7 z6)) (And (Eq y6 y0) (Eq x7 y6))) := by permutateOr lean_s590, [1, 0], (- 1)
have lean_s592 : (Or (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (Not (And (Eq z6 y0) (Eq x7 z6)))) := @cnfOrNeg [(And (Eq y6 y0) (Eq x7 y6)), (And (Eq z6 y0) (Eq x7 z6))] 1
let lean_s593 := by R1 lean_s591, lean_s592, (And (Eq z6 y0) (Eq x7 z6)), [(- 1), (- 1)]
have lean_s594 : (Or (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (Not (And (Eq y6 y0) (Eq x7 y6)))) := @cnfOrNeg [(And (Eq y6 y0) (Eq x7 y6)), (And (Eq z6 y0) (Eq x7 z6))] 0
have lean_s595 : (Or (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6)))) := by R1 lean_s593, lean_s594, (And (Eq y6 y0) (Eq x7 y6)), [1, (- 1)]
have lean_s596 : (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))) := by factor lean_s595, 1
have lean_s597 : (Eq x7 y0) := by R2 lean_s589, lean_s596, (Or (And (Eq y6 y0) (Eq x7 y6)) (And (Eq z6 y0) (Eq x7 z6))), [(- 1), 0]
have lean_s598 : (Not (Eq x13 x12)) := by R2 lean_s586, lean_s597, (Eq x7 y0), [(- 1), 0]
have lean_s599 : (Not (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12)))) := by R1 lean_s546, lean_s598, (Eq x13 x12), [(- 1), 0]
have lean_s600 : (Not (And (Eq z12 x12) (Eq x13 z12))) := by R1 lean_s543, lean_s599, (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))), [(- 1), 0]
let lean_s601 := by R1 lean_s542, lean_s600, (And (Eq z12 x12) (Eq x13 z12)), [(- 1), 0]
have lean_s602 : (Or (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))) (Not (And (Eq x12 y12) (Eq x13 y12)))) := @cnfOrNeg [(And (Eq x12 y12) (Eq x13 y12)), (And (Eq z12 x12) (Eq x13 z12))] 0
have lean_s603 : (Not (And (Eq x12 y12) (Eq x13 y12))) := by R1 lean_s602, lean_s599, (Or (And (Eq x12 y12) (Eq x13 y12)) (And (Eq z12 x12) (Eq x13 z12))), [(- 1), 0]
exact (show False from by R1 lean_s601, lean_s603, (And (Eq x12 y12) (Eq x13 y12)), [0, 0])
