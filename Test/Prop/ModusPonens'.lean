import Smt

theorem modus_ponens' (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [hp, hpq]
  simp_all
