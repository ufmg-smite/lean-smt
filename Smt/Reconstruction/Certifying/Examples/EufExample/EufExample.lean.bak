import Meta.Boolean
 
universe u
 
variable {U : Type u}
 
variable {f : U → U → U}
 
variable {p₁ p₂ p₃ : Prop}
 
variable {a b c d : U}
 
def let1' := a = b
macro "let1" : term => `(@let1' U a b)
 
def let2' := c = d
macro "let2" : term => `(@let2' U c d)
 
def let3' := p₁ ∧ True
macro "let3" : term => `(@let3' p₁)
 
def let4' := p₂ ∧ p₃
macro "let4" : term => `(@let4' p₂ p₃)
 
def let5' := (¬ p₁) ∨ let4
macro "let5" : term => `(@let5' p₁ p₂ p₃)
 
def let6' := f a c = f b d
macro "let6" : term => `(@let6' U f a b c d)
 
def let7' := ¬ let6
macro "let7" : term => `(@let7' U f a b c d)
 
def let8' := (¬ p₃) ∨ let7
macro "let8" : term => `(@let8' U f p₃ a b c d)
 
def let9' := ¬ let4
macro "let9" : term => `(@let9' p₂ p₃)
 
def let10' := ¬ let2
macro "let10" : term => `(@let10' U c d)
 
def let11' := ¬ let1
macro "let11" : term => `(@let11' U a b)
 
def let12' := let1 ∧ let2
macro "let12" : term => `(@let12' U a b c d)

theorem euf : let1 → let2 → let3 → let5 → let8 → False :=
  fun lean_a0 : let1 =>
  fun lean_a1 : let2 =>
  fun lean_a2 : let3 =>
  fun lean_a3 : let5 =>
  fun lean_a4 : let8 =>
    have lean_s0 : let12 ∨ let11 ∨ let10 := cnfAndNeg [let1, let2]
    have lean_s1 : let11 ∨ let10 ∨ let6 :=
      scope (λ lean_a5 : let1 =>
        (scope (λ lean_a6 : let2 =>
          let lean_s1 : f = f := rfl
          have lean_s2 : b = a := Eq.symm lean_a5
          have lean_s3 : let1 := Eq.symm lean_s2
          let lean_s4 := cong lean_s1 lean_s3
          have lean_s5 : d = c := Eq.symm lean_a6
          have lean_s6 : let2 := Eq.symm lean_s5
          have lean_s7 : let6 := cong lean_s4 lean_s6
          show let6 from lean_s7
        )
      ))
    have lean_s2 : let12 → let6 := by liftNOrToImp lean_s1, 2, bla; exact bla
    have lean_s3 : (¬ let12) ∨ let6 := impliesElim lean_s2
    -- let lean_s4 := clOr lean_s3
    sorry
 
