import Smt
import Smt.Rat

namespace Smt.Translate.Rat

open Qq
open Translator Term

@[smt_translate] def translateType : Translator := fun (e : Q(Type)) => match e with
  | ~q(Rat) => return symbolT "Real"
  | _       => return none

@[smt_translate] def translateRat : Translator := fun (e : Q(Rat)) => match e with
  | ~q(OfNat.ofNat $n) => return if let some n := n.rawNatLit? then literalT s!"{n}.0" else none
  | ~q(-$x)     => return appT (symbolT "-") (← applyTranslators! x)
  | ~q($x + $y) => return mkApp2 (symbolT "+") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x - $y) => return mkApp2 (symbolT "-") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x * $y) => return mkApp2 (symbolT "*") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x / $y) => return mkApp2 (symbolT "/") (← applyTranslators! x) (← applyTranslators! y)
  | _           => return none

@[smt_translate] def translateProp : Translator := fun (e : Q(Prop)) => match e with
  | ~q(($x : Rat) < $y) => return mkApp2 (symbolT "<") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(($x : Rat) ≤ $y) => return mkApp2 (symbolT "<=") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(($x : Rat) ≥ $y) => return mkApp2 (symbolT ">=") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(($x : Rat) > $y) => return mkApp2 (symbolT ">") (← applyTranslators! x) (← applyTranslators! y)
  | _                   => return none

end Smt.Translate.Rat

example {x y : Rat} {f : Rat → Rat} : ¬(((1/2 : Rat) = 1/2) ∧ x ≤ y ∧ y ≤ x ∧ ¬f x = f y) := by
  smt

example {x y : Rat} {f : Rat → Rat} : ¬(((1/2 : Int) = 1/2) ∧ x ≤ y ∧ y ≤ x ∧ ¬f x = f y) := by
  smt

example (A B : Rat) (h : 0 < A * B) : 0 < A*B/8 := by
  smt [h]

example (A B : Rat) (h : 0 < A * B) : 0 < A/8*B := by
  smt [h]

example (ε : Rat) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε := by
  smt [h1]

example (x y z : Rat) (h1 : 2*x < 3*y) (h2 : -4*x + z/2 < 0)
        (h3 : 12*y - z < 0)  : False := by
  smt [h1, h2, h3]

example (ε : Rat) (h1 : ε > 0) : ε / 2 < ε := by
  smt [h1]

example (ε : Rat) (h1 : ε > 0) : ε / 3 + ε / 3 + ε / 3 = ε := by
  smt [h1]

example (x : Rat) (h : 0 < x) : 0 < x/1 := by
  smt [h]

example (x : Rat) (h : x < 0) : 0 < x/(-1) := by
  smt [h]

example (x : Rat) (h : x < 0) : 0 < x/(-2) := by
  smt [h]

example (x : Rat) (h : x < 0) : 0 < x/(-4/5) := by
  smt [h]

example (x : Rat) (h : 0 < x) : 0 < x/2/3 := by
  smt [h]

example (x : Rat) (h : 0 < x) : 0 < x/(2/3) := by
  smt [h]

-- example (a b c : Rat) (h2 : b + 2 > 3 + b) : False := by
--   smt [h2]
--   all_goals (ring_nf; simp)
--   norm_num

-- example (a b c : Rat) (h2 : b + 2 > 3 + b) : False := by
--   smt [h2]
--   all_goals (ring_nf; simp)
--   norm_num

example (g v V c h : Rat) (h1 : h = 0) (h2 : v = V) (h3 : V > 0) (h4 : g > 0)
    (h5 : 0 ≤ c) (h6 : c < 1) : v ≤ V := by
  smt [h1, h2, h3, h4, h5, h6]

example (a b c : Rat) (h1 : a > 0) (h2 : b > 5) (h3 : c < -10) (h4 : a + b - c < 3) : False := by
  smt [h1, h2, h3, h4]

example (a b c : Rat) (h2 : b > 0) (h3 : ¬ b ≥ 0) : False := by
  smt [h2, h3]

example (x y z : Rat) (hx : x ≤ 3*y) (h2 : y ≤ 2*z) (h3 : x ≥ 6*z) : x = 3*y := by
  smt [hx, h2, h3]

example (x y z : Rat) (hx : ¬ x > 3*y) (h2 : ¬ y > 2*z) (h3 : x ≥ 6*z) : x = 3*y := by
  smt [hx, h2, h3]

-- example (x y : Rat) (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3) (h' : (x + 4) * x ≥ 0)
--     (h'' : (6 + 3 * y) * y ≥ 0) : False := by
--   smt [h, h'']
--   all_goals sorry

example (a : Rat) (ha : 0 ≤ a) : 0 * 0 ≤ 2 * a := by
  smt [ha]

example (x y : Rat) (h : x < y) : x ≠ y := by
  smt [h]

example (x y : Rat) (h : x < y) : ¬ x = y := by
  smt [h]

-- example (x : Rat) : id x ≥ x := by
--   let idℝ := fun (x : Rat) => x
--   let hidℝ : idℝ = fun x => x := rfl
--   have : @id Rat = idℝ := rfl
--   rewrite [this]
--   smt [idℝ]
--   all_goals (ring_nf; simp)
--   sorry

example (prime : Int → Prop) (x y z : Rat) (h1 : 2*x + ((-3)*y) < 0) (h2 : (-4)*x + 2*z < 0) (h3 : 12*y + (-4)* z < 0)
    (h4 : prime 7) : False := by
  smt [h1, h2, h3, h4]

example (prime : Int → Prop) (x y z : Rat) (h1 : 2*1*x + (3)*(y*(-1)) < 0) (h2 : (-2)*x*2 < -(z + z))
    (h3 : 12*y + (-4)* z < 0) (h4 : prime 7) : False := by
  smt [h1, h2, h3, h4]

example : ∃ (x : Rat), x > 2 ∧ x * x < 24 := by
  smt

example : ∃ (x : Rat), x > 2 ∧ x * 2 < 24 := by
  smt
