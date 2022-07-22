import Smt

open Lean Meta Elab Tactic in
elab "extract_def" i:ident : tactic => do
  let nm ← resolveGlobalConstNoOverloadWithInfo i
  let _ ← Smt.addEqnDefForConst nm

def foo : Int := 10

example : foo = 10 := by
  extract_def foo
  exact foo.def

def bar (a b : Int) : Int := a + b

example : bar 2 3 = 2 + 3 := by
  extract_def bar
  exact bar.def 2 3

def baz (a : Int) : Int → Int := (a + ·)

example : baz 2 3 = 2 + 3 := by
  extract_def baz
  exact baz.def 2 3

def baw (a : Int) : Int → Int := Int.add a

example : baw 2 3 = 2 + 3 := by
  extract_def baw
  exact baw.def 2 3
