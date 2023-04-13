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

theorem th0 : (Eq (Eq (f (f (f (f (f (f x)))))) (f (f x))) (Eq (f (f x)) (f (f (f (f (f (f x)))))))) → (Eq (Eq (f (f (f (f (f x))))) (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) → (Eq (Eq (f (f (f (f (f (f x)))))) (f (f (f (f x))))) (Eq (f (f (f (f x)))) (f (f (f (f (f (f x)))))))) → (Eq (Eq (f (f (f (f x)))) (f (f x))) (Eq (f (f x)) (f (f (f (f x)))))) → (Not (Implies (And (Eq (f (f (f (f (f (f x)))))) (f (f x))) (Eq (f (f (f (f (f x))))) (f (f (f x))))) (And (Eq (f (f (f (f x)))) (f (f x))) (Eq (f (f (f (f (f (f x)))))) (f (f (f (f x)))))))) → False :=
fun lean_r0 : (Eq (Eq (f (f (f (f (f (f x)))))) (f (f x))) (Eq (f (f x)) (f (f (f (f (f (f x)))))))) =>
fun lean_r1 : (Eq (Eq (f (f (f (f (f x))))) (f (f (f x)))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) =>
fun lean_r2 : (Eq (Eq (f (f (f (f (f (f x)))))) (f (f (f (f x))))) (Eq (f (f (f (f x)))) (f (f (f (f (f (f x)))))))) =>
fun lean_r3 : (Eq (Eq (f (f (f (f x)))) (f (f x))) (Eq (f (f x)) (f (f (f (f x)))))) =>
fun lean_a4 : (Not (Implies (And (Eq (f (f (f (f (f (f x)))))) (f (f x))) (Eq (f (f (f (f (f x))))) (f (f (f x))))) (And (Eq (f (f (f (f x)))) (f (f x))) (Eq (f (f (f (f (f (f x)))))) (f (f (f (f x)))))))) => by
let lean_s0 := flipCongrArg lean_r0 [And]
have lean_s1 : (Eq (And (Eq (f (f (f (f (f (f x)))))) (f (f x))) (Eq (f (f (f (f (f x))))) (f (f (f x))))) (And (Eq (f (f x)) (f (f (f (f (f (f x))))))) (Eq (f (f (f x))) (f (f (f (f (f x)))))))) := congr lean_s0 lean_r1
let lean_s2 := flipCongrArg lean_s1 [Implies]
let lean_s3 := flipCongrArg lean_r3 [And]
have lean_s4 : (Eq (And (Eq (f (f (f (f x)))) (f (f x))) (Eq (f (f (f (f (f (f x)))))) (f (f (f (f x)))))) (And (Eq (f (f x)) (f (f (f (f x))))) (Eq (f (f (f (f x)))) (f (f (f (f (f (f x))))))))) := congr lean_s3 lean_r2
have lean_s5 : (Eq (Implies (And (Eq (f (f (f (f (f (f x)))))) (f (f x))) (Eq (f (f (f (f (f x))))) (f (f (f x))))) (And (Eq (f (f (f (f x)))) (f (f x))) (Eq (f (f (f (f (f (f x)))))) (f (f (f (f x))))))) (Implies (And (Eq (f (f x)) (f (f (f (f (f (f x))))))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) (And (Eq (f (f x)) (f (f (f (f x))))) (Eq (f (f (f (f x)))) (f (f (f (f (f (f x)))))))))) := congr lean_s2 lean_s4
have lean_s6 : (Eq (Not (Implies (And (Eq (f (f (f (f (f (f x)))))) (f (f x))) (Eq (f (f (f (f (f x))))) (f (f (f x))))) (And (Eq (f (f (f (f x)))) (f (f x))) (Eq (f (f (f (f (f (f x)))))) (f (f (f (f x)))))))) (Not (Implies (And (Eq (f (f x)) (f (f (f (f (f (f x))))))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) (And (Eq (f (f x)) (f (f (f (f x))))) (Eq (f (f (f (f x)))) (f (f (f (f (f (f x))))))))))) := flipCongrArg lean_s5 [Not]
have lean_s7 : (Not (Implies (And (Eq (f (f x)) (f (f (f (f (f (f x))))))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) (And (Eq (f (f x)) (f (f (f (f x))))) (Eq (f (f (f (f x)))) (f (f (f (f (f (f x)))))))))) := eqResolve lean_a4 lean_s6
have lean_s8 : (Not (And (Eq (f (f x)) (f (f (f (f x))))) (Eq (f (f (f (f x)))) (f (f (f (f (f (f x))))))))) := notImplies2 lean_s7
have lean_s9 : (Or (Not (Eq (f (f x)) (f (f (f (f x)))))) (Not (Eq (f (f (f (f x)))) (f (f (f (f (f (f x))))))))) := flipNotAnd lean_s8 [(Eq (f (f x)) (f (f (f (f x))))), (Eq (f (f (f (f x)))) (f (f (f (f (f (f x)))))))]
have lean_s10 : (Or (And (Eq (f (f (f x))) (f (f (f (f (f x)))))) (Eq (f (f x)) (f (f (f (f (f (f x)))))))) (Or (Not (Eq (f (f (f x))) (f (f (f (f (f x))))))) (Not (Eq (f (f x)) (f (f (f (f (f (f x)))))))))) := cnfAndNeg [(Eq (f (f (f x))) (f (f (f (f (f x)))))), (Eq (f (f x)) (f (f (f (f (f (f x)))))))]
have lean_s11 : (Or (Not (Eq (f (f (f x))) (f (f (f (f (f x))))))) (Or (Not (Eq (f (f x)) (f (f (f (f (f (f x)))))))) (Eq (f (f x)) (f (f (f (f x))))))) :=
  (scope (fun lean_a5 : (Eq (f (f (f x))) (f (f (f (f (f x)))))) =>
    (scope (fun lean_a6 : (Eq (f (f x)) (f (f (f (f (f (f x))))))) =>
      have lean_s11 : (Eq (f (f (f (f (f (f x)))))) (f (f x))) := Eq.symm lean_a6
      have lean_s12 : (Eq (f (f x)) (f (f (f (f (f (f x))))))) := Eq.symm lean_s11
      have lean_s13 : (Eq (f (f (f (f (f x))))) (f (f (f x)))) := Eq.symm lean_a5
      have lean_s14 : (Eq (f (f (f (f (f (f x)))))) (f (f (f (f x))))) := flipCongrArg lean_s13 [f]
      have lean_s15 : (Eq (f (f x)) (f (f (f (f x))))) := Eq.trans lean_s12 lean_s14
      show (Eq (f (f x)) (f (f (f (f x))))) from lean_s15
  ))))
have lean_s12 : (Implies (And (Eq (f (f (f x))) (f (f (f (f (f x)))))) (Eq (f (f x)) (f (f (f (f (f (f x)))))))) (Eq (f (f x)) (f (f (f (f x)))))) := by liftOrNToImp lean_s11, 2
have lean_s13 : (Or (Not (And (Eq (f (f (f x))) (f (f (f (f (f x)))))) (Eq (f (f x)) (f (f (f (f (f (f x))))))))) (Eq (f (f x)) (f (f (f (f x)))))) := impliesElim lean_s12
have lean_s14 : (Or (Not (Eq (f (f (f x))) (f (f (f (f (f x))))))) (Or (Not (Eq (f (f x)) (f (f (f (f (f (f x)))))))) (Eq (f (f x)) (f (f (f (f x))))))) := by R1 lean_s10, lean_s13, (And (Eq (f (f (f x))) (f (f (f (f (f x)))))) (Eq (f (f x)) (f (f (f (f (f (f x)))))))), [(- 1), (- 1)]
have lean_s15 : (Or (Eq (f (f x)) (f (f (f (f x))))) (Or (Not (Eq (f (f x)) (f (f (f (f (f (f x)))))))) (Not (Eq (f (f (f x))) (f (f (f (f (f x))))))))) := by permutateOr lean_s14, [2, 1, 0], (- 1)
have lean_s16 : (And (Eq (f (f x)) (f (f (f (f (f (f x))))))) (Eq (f (f (f x))) (f (f (f (f (f x))))))) := notImplies1 lean_s7
have lean_s17 : (Eq (f (f x)) (f (f (f (f (f (f x))))))) := by andElim lean_s16, 0
let lean_s18 := by R2 lean_s15, lean_s17, (Eq (f (f x)) (f (f (f (f (f (f x))))))), [(- 1), 0]
have lean_s19 : (Eq (f (f (f x))) (f (f (f (f (f x)))))) := by andElim lean_s16, 1
have lean_s20 : (Eq (f (f x)) (f (f (f (f x))))) := by R2 lean_s18, lean_s19, (Eq (f (f (f x))) (f (f (f (f (f x)))))), [(- 1), 0]
let lean_s21 := by R2 lean_s9, lean_s20, (Eq (f (f x)) (f (f (f (f x))))), [(- 1), 0]
have lean_s22 : (Or (Not (Eq (f (f (f x))) (f (f (f (f (f x))))))) (Eq (f (f (f (f x)))) (f (f (f (f (f (f x)))))))) :=
  (scope (fun lean_a7 : (Eq (f (f (f x))) (f (f (f (f (f x)))))) =>
    have lean_s22 : (Eq (f (f (f (f (f x))))) (f (f (f x)))) := Eq.symm lean_a7
    have lean_s23 : (Eq (f (f (f x))) (f (f (f (f (f x)))))) := Eq.symm lean_s22
    have lean_s24 : (Eq (f (f (f (f x)))) (f (f (f (f (f (f x))))))) := flipCongrArg lean_s23 [f]
    show (Eq (f (f (f (f x)))) (f (f (f (f (f (f x))))))) from lean_s24
  ))
have lean_s23 : (Implies (Eq (f (f (f x))) (f (f (f (f (f x)))))) (Eq (f (f (f (f x)))) (f (f (f (f (f (f x)))))))) := by liftOrNToImp lean_s22, 1
have lean_s24 : (Or (Not (Eq (f (f (f x))) (f (f (f (f (f x))))))) (Eq (f (f (f (f x)))) (f (f (f (f (f (f x)))))))) := impliesElim lean_s23
have lean_s25 : (Or (Eq (f (f (f (f x)))) (f (f (f (f (f (f x))))))) (Not (Eq (f (f (f x))) (f (f (f (f (f x)))))))) := by permutateOr lean_s24, [1, 0], (- 1)
have lean_s26 : (Eq (f (f (f (f x)))) (f (f (f (f (f (f x))))))) := by R2 lean_s25, lean_s19, (Eq (f (f (f x))) (f (f (f (f (f x)))))), [(- 1), 0]
exact (show False from by R2 lean_s21, lean_s26, (Eq (f (f (f (f x)))) (f (f (f (f (f (f x))))))), [0, 0])
