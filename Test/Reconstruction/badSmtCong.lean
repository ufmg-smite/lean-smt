import Smt.Reconstruction.Certifying.Boolean

universe u
variable {B : Type u}
variable {A : Type u}
variable {a : A}
variable {b : A}
variable {x : A}
variable {f : (A -> B)}
variable {y : A}

example : (Iff (Not (Not (Eq y a))) (Eq y a)) → (Iff (Iff (Eq y a) (Not (Not (Eq y a)))) (Iff (Eq y a) (Eq y a))) := by
  intros h1
  have lean_s24 : (Eq Iff Iff) := rfl
  have lean_s25 : (Iff (Eq y a) (Eq y a)) := Iff.rfl
  let lean_s26 := by smtCong lean_s24, lean_s25
  smtCong lean_s26, h1
  /- exact smtCong₄ lean_s26 h1 -/
