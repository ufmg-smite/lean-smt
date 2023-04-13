import Smt.Reconstruction.Certifying

open Classical
open Smt.Reconstruction.Certifying



set_option maxRecDepth 10000
set_option maxHeartbeats 500000


universe u
variable {A : Type u} [Nonempty A]
variable {x : A}
variable {x : A}
variable {f : (A -> A)}
variable {f : (A -> A)}

theorem th0 : (Eq (Eq (f (f (f (f x)))) (f x)) (Eq (f x) (f (f (f (f x)))))) → (Eq (Eq (f (f x)) (f x)) (Eq (f x) (f (f x)))) → (Eq (Eq (f (f (f (f (f (f x)))))) (f x)) (Eq (f x) (f (f (f (f (f (f x)))))))) → (Not (Implies (And (Eq (f (f (f (f x)))) (f x)) (Eq (f (f (f (f (f (f x)))))) (f x))) (Eq (f (f x)) (f x)))) → False :=
fun lean_r0 : (Eq (Eq (f (f (f (f x)))) (f x)) (Eq (f x) (f (f (f (f x)))))) =>
fun lean_r1 : (Eq (Eq (f (f x)) (f x)) (Eq (f x) (f (f x)))) =>
fun lean_r2 : (Eq (Eq (f (f (f (f (f (f x)))))) (f x)) (Eq (f x) (f (f (f (f (f (f x)))))))) =>
fun lean_a3 : (Not (Implies (And (Eq (f (f (f (f x)))) (f x)) (Eq (f (f (f (f (f (f x)))))) (f x))) (Eq (f (f x)) (f x)))) => by
have lean_s0 : (Or (And (Eq (f x) (f (f (f (f (f (f x))))))) (Eq (f x) (f (f (f (f x)))))) (Or (Not (Eq (f x) (f (f (f (f (f (f x)))))))) (Not (Eq (f x) (f (f (f (f x)))))))) := cnfAndNeg [(Eq (f x) (f (f (f (f (f (f x))))))), (Eq (f x) (f (f (f (f x)))))]
have lean_s1 : (Or (Not (Eq (f x) (f (f (f (f (f (f x)))))))) (Or (Not (Eq (f x) (f (f (f (f x)))))) (Eq (f x) (f (f x))))) :=
  (scope (fun lean_a4 : (Eq (f x) (f (f (f (f (f (f x))))))) =>
    (scope (fun lean_a5 : (Eq (f x) (f (f (f (f x))))) =>
      have lean_s1 : (Eq (f (f (f (f x)))) (f x)) := Eq.symm lean_a5
      have lean_s2 : (Eq (f x) (f (f (f (f x))))) := Eq.symm lean_s1
      have lean_s3 : (Eq (f (f x)) (f (f (f (f (f x)))))) := flipCongrArg lean_s2 [f]
      have lean_s4 : (Eq (f (f (f x))) (f (f (f (f (f (f x))))))) := flipCongrArg lean_s3 [f]
      have lean_s5 : (Eq (f (f (f (f (f (f x)))))) (f x)) := Eq.symm lean_a4
      have lean_s6 : (Eq (f (f (f x))) (f x)) := Eq.trans lean_s4 lean_s5
      have lean_s7 : (Eq (f (f (f (f x)))) (f (f x))) := flipCongrArg lean_s6 [f]
      have lean_s8 : (Eq (f x) (f (f x))) := Eq.trans lean_s2 lean_s7
      show (Eq (f x) (f (f x))) from lean_s8
  ))))
have lean_s2 : (Implies (And (Eq (f x) (f (f (f (f (f (f x))))))) (Eq (f x) (f (f (f (f x)))))) (Eq (f x) (f (f x)))) := by liftOrNToImp lean_s1, 2
have lean_s3 : (Or (Not (And (Eq (f x) (f (f (f (f (f (f x))))))) (Eq (f x) (f (f (f (f x))))))) (Eq (f x) (f (f x)))) := impliesElim lean_s2
have lean_s4 : (Or (Not (Eq (f x) (f (f (f (f (f (f x)))))))) (Or (Not (Eq (f x) (f (f (f (f x)))))) (Eq (f x) (f (f x))))) := by R1 lean_s0, lean_s3, (And (Eq (f x) (f (f (f (f (f (f x))))))) (Eq (f x) (f (f (f (f x)))))), [(- 1), (- 1)]
have lean_s5 : (Or (Eq (f x) (f (f x))) (Or (Not (Eq (f x) (f (f (f (f x)))))) (Not (Eq (f x) (f (f (f (f (f (f x)))))))))) := by permutateOr lean_s4, [2, 1, 0], (- 1)
let lean_s6 := flipCongrArg lean_r0 [And]
have lean_s7 : (Eq (And (Eq (f (f (f (f x)))) (f x)) (Eq (f (f (f (f (f (f x)))))) (f x))) (And (Eq (f x) (f (f (f (f x))))) (Eq (f x) (f (f (f (f (f (f x))))))))) := congr lean_s6 lean_r2
let lean_s8 := flipCongrArg lean_s7 [Implies]
have lean_s9 : (Eq (Implies (And (Eq (f (f (f (f x)))) (f x)) (Eq (f (f (f (f (f (f x)))))) (f x))) (Eq (f (f x)) (f x))) (Implies (And (Eq (f x) (f (f (f (f x))))) (Eq (f x) (f (f (f (f (f (f x)))))))) (Eq (f x) (f (f x))))) := congr lean_s8 lean_r1
have lean_s10 : (Eq (Not (Implies (And (Eq (f (f (f (f x)))) (f x)) (Eq (f (f (f (f (f (f x)))))) (f x))) (Eq (f (f x)) (f x)))) (Not (Implies (And (Eq (f x) (f (f (f (f x))))) (Eq (f x) (f (f (f (f (f (f x)))))))) (Eq (f x) (f (f x)))))) := flipCongrArg lean_s9 [Not]
have lean_s11 : (Not (Implies (And (Eq (f x) (f (f (f (f x))))) (Eq (f x) (f (f (f (f (f (f x)))))))) (Eq (f x) (f (f x))))) := eqResolve lean_a3 lean_s10
have lean_s12 : (Not (Eq (f x) (f (f x)))) := notImplies2 lean_s11
let lean_s13 := by R1 lean_s5, lean_s12, (Eq (f x) (f (f x))), [(- 1), 0]
have lean_s14 : (And (Eq (f x) (f (f (f (f x))))) (Eq (f x) (f (f (f (f (f (f x)))))))) := notImplies1 lean_s11
have lean_s15 : (Eq (f x) (f (f (f (f (f (f x))))))) := by andElim lean_s14, 1
let lean_s16 := by R2 lean_s13, lean_s15, (Eq (f x) (f (f (f (f (f (f x))))))), [(- 1), 0]
have lean_s17 : (Eq (f x) (f (f (f (f x))))) := by andElim lean_s14, 0
exact (show False from by R2 lean_s16, lean_s17, (Eq (f x) (f (f (f (f x))))), [0, 0])
