import Smt

def MyInt := Int
def MyInt.add (a b : MyInt) : MyInt := @HAdd.hAdd Int Int _ _ a b

example (a b : MyInt) : a.add b = b.add a := by
  smt_show [MyInt, MyInt.add]
  sorry
