import Smt

variable {G : Type} [Nonempty G] (op : G → G → G) (inv : G → G) (e : G)

axiom assoc   : ∀ a b c, op a (op b c) = op (op a b) c
axiom inverse : ∀ a, op (inv a) a = e
axiom ident   : ∀ a, op e a = a

theorem inverse' : ∀ a, op a (inv a) = e := by
  smt [assoc op, inverse op inv e, ident op e]
  all_goals simp [eq_comm, Classical.not_not]

theorem identity' : ∀ a, op a e = a := by
  smt [assoc op, inverse op inv e, ident op e, inverse' op inv e]
  all_goals simp [eq_comm, Classical.not_not]

theorem unique_identity e' : (∀ z, op e' z = z) → e' = e := by
  smt [assoc op, inverse op inv e, ident op e]
  all_goals simp [eq_comm]
