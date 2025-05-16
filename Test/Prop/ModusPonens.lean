import Smt

theorem modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt +showQuery
  exact hpq hp

example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [hp, hpq]

example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [*]

example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt (timeout := .some 1) [*]
