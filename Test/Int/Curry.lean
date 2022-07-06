import Smt

def myAdd : Int → Int → Int := Int.add

example (a b : Int) : myAdd a b = myAdd b a := by
  smt [myAdd]
  sorry

example (a b : Int) : let myAdd' := Int.add; myAdd' a b = myAdd' b a := by
  intro myAdd'
  smt [myAdd']
  sorry
