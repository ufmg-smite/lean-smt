import Smt

theorem funextEq {α β : Type} (f g : α → β) :
  (f = g) = ∀ x, f x = g x := by
  apply propext
  constructor
  { intro h ; simp only [h, implies_true] }
  { intro h ; apply funext h }

set_option trace.smt true in
theorem extracted {node round value : Type}
  (rel : node → round → round → value → Bool)
  (upd_rel : node → round → round → value → Bool)
  (hnext : upd_rel = rel)
  : True := by
  simp only [funextEq] at hnext
  -- After the simplification, `hnext` is pretty-printed as:
  -- (hnext : (∀ (x : node) (x_1 x_2 : round) (x_3 : value), upd_rel x x_1 x_2 x_3 = rel x x_1 x_2 x_3))
  -- but the binders actually all have name `x`
  smt [hnext]
