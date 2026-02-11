import Smt

@[smt_normalize]
def curryAdd : Int → Int → Int := HAdd.hAdd

example (a b : Int) : curryAdd a b = curryAdd b a := by
  smt

@[smt_normalize]
def partCurryAdd (a : Int) : Int → Int := HAdd.hAdd a

example (a b : Int) : partCurryAdd a b = partCurryAdd b a := by
  smt

example (a b : Int)
    : let partCurryAdd' := fun a => HAdd.hAdd a;
    partCurryAdd' a b = partCurryAdd' b a := by
  smt +mono

set_option linter.unusedVariables false in
@[smt_normalize]
def mismatchNamesAdd : ∀ (a b : Int), Int := fun c d => c + d

example (a b : Int) : mismatchNamesAdd a b = mismatchNamesAdd b a := by
  smt
