import Smt

theorem out_arity_5 {α : Type} [Nonempty α] (r : α → α → α → α → α → Bool) (a b : α)
    (h : ∀ x y z u v, r x y z u v = true → x ≠ y) (hab : r a b a b a = true) : a ≠ b := by
  smt [h, hab]

theorem out_arity_6 {α : Type} [Nonempty α] (r : α → α → α → α → α → α → Bool) (a b : α)
    (h : ∀ x y z u v w, r x y z u v w = true → x ≠ y) (hab : r a b a b a b = true) : a ≠ b := by
  smt [h, hab]

theorem in_arity_5 {α : Type} [Nonempty α] (f : α → α → α → α → Bool → α) (a : α)
    (h : ∀ x y z u (b : Bool), f x y z u b = x) : f a a a a true = a := by
  smt [h]

theorem in_arity_6 {α : Type} [Nonempty α] (f : α → α → α → α → α → Bool → α) (a : α)
    (h : ∀ x y z u v (b : Bool), f x y z u v b = x) : f a a a a a true = a := by
  smt [h]
