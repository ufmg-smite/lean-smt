import Smt

def MyInt := Int
def MyInt.add (a b : MyInt) : MyInt := Int.add a b

example (a b : MyInt) : a.add b = b.add a := by
  smt [MyInt, MyInt.add]
  sorry
