import Smt

def curryAdd : Int → Int → Int := HAdd.hAdd

example (a b : Int) : curryAdd a b = curryAdd b a := by
  smt_show [curryAdd]
  sorry

def partCurryAdd (a : Int) : Int → Int := HAdd.hAdd a

example (a b : Int) : partCurryAdd a b = partCurryAdd b a := by
  smt_show [partCurryAdd]
  sorry

example (a b : Int)
    : let partCurryAdd' := fun a => HAdd.hAdd a;
    partCurryAdd' a b = partCurryAdd' b a := by
  intro partCurryAdd'
  smt_show [partCurryAdd']
  sorry

set_option linter.unusedVariables false in
def mismatchNamesAdd : ∀ (a b : Int), Int := fun c d => c + d

example (a b : Int) : mismatchNamesAdd a b = mismatchNamesAdd b a := by
  smt_show [mismatchNamesAdd]
  sorry
