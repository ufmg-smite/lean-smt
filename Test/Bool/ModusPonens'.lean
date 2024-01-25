import Smt

theorem modus_ponens' (p q : Bool) (hp : p) (hpq : p → q) : q := by
  smt_show [hp, hpq]
  simp_all
