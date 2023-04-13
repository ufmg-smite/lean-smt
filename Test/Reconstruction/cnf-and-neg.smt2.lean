import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {I : Type u} [Nonempty I]
variable {b : I}
variable {a : I}
variable {a : I}
variable {f : (I -> I)}
variable {c : I}
variable {c : I}
variable {b : I}
variable {f : (I -> I)}

theorem th0 : (Eq (Eq (Not (Not (Eq a b))) (Eq a b)) (Eq (Eq a b) (Not (Not (Eq a b))))) → (Eq (Not (Not (Eq a c))) (Eq a c)) → (Eq (Eq (Not (Not (Eq a c))) (Eq a c)) (Eq (Eq a c) (Not (Not (Eq a c))))) → (Eq (Eq (Eq a c) (Eq a c)) True) → (Eq (Eq (Eq a b) (Eq a b)) True) → (Eq (Not (Not (Eq a b))) (Eq a b)) → (Not (Eq (f a) (f b))) → (Not (Eq (f a) (f c))) → (Not (And (Not (Eq a b)) (Not (Eq a c)))) → False :=
fun lean_r0 : (Eq (Eq (Not (Not (Eq a b))) (Eq a b)) (Eq (Eq a b) (Not (Not (Eq a b))))) =>
fun lean_r1 : (Eq (Not (Not (Eq a c))) (Eq a c)) =>
fun lean_r2 : (Eq (Eq (Not (Not (Eq a c))) (Eq a c)) (Eq (Eq a c) (Not (Not (Eq a c))))) =>
fun lean_r3 : (Eq (Eq (Eq a c) (Eq a c)) True) =>
fun lean_r4 : (Eq (Eq (Eq a b) (Eq a b)) True) =>
fun lean_r5 : (Eq (Not (Not (Eq a b))) (Eq a b)) =>
fun lean_a6 : (Not (Eq (f a) (f b))) =>
fun lean_a7 : (Not (Eq (f a) (f c))) =>
fun lean_a8 : (Not (And (Not (Eq a b)) (Not (Eq a c)))) => by
have lean_s0 : (Or (Not (Eq a b)) (Eq (f a) (f b))) :=
  (scope (fun lean_a9 : (Eq a b) =>
    have lean_s0 : (Eq b a) := Eq.symm lean_a9
    have lean_s1 : (Eq a b) := Eq.symm lean_s0
    have lean_s2 : (Eq (f a) (f b)) := flipCongrArg lean_s1 [f]
    show (Eq (f a) (f b)) from lean_s2
  ))
have lean_s1 : (Implies (Eq a b) (Eq (f a) (f b))) := by liftOrNToImp lean_s0, 1
have lean_s2 : (Or (Not (Eq a b)) (Eq (f a) (f b))) := impliesElim lean_s1
have lean_s3 : (Or (Eq (f a) (f b)) (Not (Eq a b))) := by permutateOr lean_s2, [1, 0], (- 1)
have lean_s4 : (Or (Not (Not (Eq a b))) (Not (Not (Eq a c)))) := flipNotAnd lean_a8 [(Not (Eq a b)), (Not (Eq a c))]
have lean_s5 : (Eq (Eq a b) (Eq a b)) := rfl
let lean_s6 := flipCongrArg lean_s5 [Eq]
have lean_s7 : (Eq (Eq (Eq a b) (Not (Not (Eq a b)))) (Eq (Eq a b) (Eq a b))) := congr lean_s6 lean_r5
have lean_s8 : (Eq (Eq (Eq a b) (Not (Not (Eq a b)))) True) := Eq.trans lean_s7 lean_r4
have lean_s9 : (Eq (Eq (Not (Not (Eq a b))) (Eq a b)) True) := Eq.trans lean_r0 lean_s8
have lean_s10 : (Eq (Not (Not (Eq a b))) (Eq a b)) := trueElim lean_s9
let lean_s11 := flipCongrArg lean_s10 [Or]
have lean_s12 : (Eq (Eq a c) (Eq a c)) := rfl
let lean_s13 := flipCongrArg lean_s12 [Eq]
have lean_s14 : (Eq (Eq (Eq a c) (Not (Not (Eq a c)))) (Eq (Eq a c) (Eq a c))) := congr lean_s13 lean_r1
have lean_s15 : (Eq (Eq (Eq a c) (Not (Not (Eq a c)))) True) := Eq.trans lean_s14 lean_r3
have lean_s16 : (Eq (Eq (Not (Not (Eq a c))) (Eq a c)) True) := Eq.trans lean_r2 lean_s15
have lean_s17 : (Eq (Not (Not (Eq a c))) (Eq a c)) := trueElim lean_s16
have lean_s18 : (Eq (Or (Not (Not (Eq a b))) (Not (Not (Eq a c)))) (Or (Eq a b) (Eq a c))) := congr lean_s11 lean_s17
have lean_s19 : (Or (Eq a b) (Eq a c)) := eqResolve lean_s4 lean_s18
have lean_s20 : (Or (Not (Eq a c)) (Eq (f a) (f c))) :=
  (scope (fun lean_a10 : (Eq a c) =>
    have lean_s20 : (Eq c a) := Eq.symm lean_a10
    have lean_s21 : (Eq a c) := Eq.symm lean_s20
    have lean_s22 : (Eq (f a) (f c)) := flipCongrArg lean_s21 [f]
    show (Eq (f a) (f c)) from lean_s22
  ))
have lean_s21 : (Implies (Eq a c) (Eq (f a) (f c))) := by liftOrNToImp lean_s20, 1
have lean_s22 : (Or (Not (Eq a c)) (Eq (f a) (f c))) := impliesElim lean_s21
have lean_s23 : (Or (Eq (f a) (f c)) (Not (Eq a c))) := by permutateOr lean_s22, [1, 0], (- 1)
have lean_s24 : (Not (Eq a c)) := by R1 lean_s23, lean_a7, (Eq (f a) (f c)), [(- 1), 0]
have lean_s25 : (Eq a b) := by R1 lean_s19, lean_s24, (Eq a c), [(- 1), 0]
let lean_s26 := by R2 lean_s3, lean_s25, (Eq a b), [(- 1), 0]
exact (show False from by R1 lean_s26, lean_a6, (Eq (f a) (f b)), [0, 0])
