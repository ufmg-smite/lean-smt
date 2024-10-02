import Smt

theorem extracted {round : Type} [round_dec : DecidableEq round]
  (st_one_a : round → Prop) (st'_one_a : round → Prop)
  (hnext : ∃ r, (∀ (x : round), st'_one_a x = if x = r then True else st_one_a x))
  : True := by
  smt [hnext]
