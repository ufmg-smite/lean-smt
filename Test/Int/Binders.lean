import Smt

def curryAdd : Int → Int → Int := Int.add

example (a b : Int) : curryAdd a b = curryAdd b a := by
  smt [curryAdd]
  sorry

def partCurryAdd (a : Int) : Int → Int := Int.add a

example (a b : Int) : partCurryAdd a b = partCurryAdd b a := by
  smt [partCurryAdd]
  sorry

example (a b : Int)
    : let partCurryAdd' := fun a => Int.add a;
    partCurryAdd' a b = partCurryAdd' b a := by
  intro partCurryAdd'
  smt [partCurryAdd']
  sorry

set_option linter.unusedVariables false in
def mismatchNamesAdd : ∀ (a b : Int), Int := fun c d => c + d

example (a b : Int) : mismatchNamesAdd a b = mismatchNamesAdd b a := by
  smt [mismatchNamesAdd]
  sorry
