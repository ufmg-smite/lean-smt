import Smt.Dsl.Sexp

namespace Smt.Reconstruction.Rewrites.Prop

@[simp] theorem bool_eq_refl : (t = t) = True := eq_self t
@[simp] theorem bool_eq_symm : (t = s) = (s = t) := propext ⟨(· ▸ rfl), (· ▸ rfl)⟩
@[simp] theorem bool_double_neg_elim : Not (Not t) = t :=
propext ⟨ match Classical.em (¬t) with
| Or.inl g1 => fun h1  => absurd g1 h1
| Or.inr _ => match Classical.em (t) with
              | Or.inl g2 => fun _ => g2
              | Or.inr g2 => fun x => absurd g2 x, 
not_not_intro⟩

@[simp] theorem bool_eq_true : (t = True) = t := propext ⟨of_eq_true, eq_true⟩
@[simp] theorem bool_eq_false : (t = False) = (Not t) := propext ⟨(· ▸ not_false), eq_false⟩

@[simp] theorem bool_impl_false1 : (t → False) = (Not t) := propext ⟨(·), (·)⟩
@[simp] theorem bool_impl_false2 : (False → t) = True := propext ⟨fun _ => trivial, fun _ => False.elim⟩
@[simp] theorem bool_impl_true1 : (t → True) = True := propext ⟨fun _ => trivial, fun _ _ => trivial⟩
@[simp] theorem bool_impl_true2 {t : Prop} : (True → t) = t := propext ⟨(· trivial), fun ht _ => ht⟩

-- theorem or_assoc : (a ∨ b ∨ c) = ((a ∨ b) ∨ c) := sorry

@[simp] theorem bool_or_true : (xs ∨ True ∨ ys) = True := Eq.symm (true_or _) ▸ or_true _
@[simp] theorem bool_or_false : (xs ∨ False ∨ ys) = (xs ∨ ys) := Eq.symm (false_or _) ▸ rfl
@[simp] theorem bool_or_flatten : (xs ∨ (b ∨ ys) ∨ zs) = (xs ∨ zs ∨ b ∨ ys) := sorry
@[simp] theorem bool_or_dup : (xs ∨ b ∨ ys ∨ b ∨ zs) = (xs ∨ b ∨ ys ∨ zs) := sorry

-- macro "bool_or_true" : tactic => `(tactic| simp only [or_true, true_or])
-- macro "bool_or_false" : tactic => `(tactic| simp only [or_false, false_or, or_assoc])

@[simp] theorem bool_and_true : (xs ∧ True ∧ ys) = (xs ∧ ys) := Eq.symm (true_and _) ▸ rfl
@[simp] theorem bool_and_false : (xs ∧ False ∧ ys) = False := Eq.symm (false_and _) ▸ and_false _
@[simp] theorem bool_and_flatten : (xs ∧ (b ∧ ys) ∧ zs) = (xs ∧ zs ∧ b ∧ ys) := sorry
@[simp] theorem bool_and_dup : (xs ∧ b ∧ ys ∧ b ∧ zs) = (xs ∧ b ∧ ys ∧ zs) := sorry

@[simp] theorem bool_ite_true_cond : ite True x y = x := rfl
@[simp] theorem bool_ite_false_cond : ite False x y = y := rfl
@[simp] theorem bool_ite_not_cond [h : Decidable c] : ite (Not c) x y = ite c y x :=
  h.byCases (fun hc => if_pos hc ▸ if_neg (not_not_intro hc) ▸ rfl)
            (fun hnc => if_pos hnc ▸ if_neg hnc ▸ rfl)

@[simp] theorem bool_and_conf : (xs ∨ w ∨ ys ∨ ¬w ∨ zs) = False := sorry
@[simp] theorem bool_or_taut : (xs ∨ w ∨ ys ∨ ¬w ∨ zs) = False := sorry

end Smt.Reconstruction.Rewrites.Prop
