import Smt.Tactic.Concretize

def generalAdd [Add α] (a b : α) := a + b

example : @generalAdd Int _ 3 3 = (6 : Int) := by
  concretize [generalAdd]
  rfl
