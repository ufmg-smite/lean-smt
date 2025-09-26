import Smt
import Smt.Preprocess.Embedding

-- Boolean tests

example (p q : Bool) (h : p && q) (h2 : p || q) : (1 : Int) + 1 = 2 := by
  smt_translate
  smt

example (p q : Bool) : (p || q) || (!p && !q) := by
  smt_translate
  smt

example (p : Bool) : (p || !p) = true := by
  smt_translate
  smt

example (p : Bool) : (p && !p) = false := by
  smt_translate
  smt

example (p q r : Bool) : (p && (q || r)) = ((p && q) || (p && r)) := by
  smt_translate
  smt

example (p q r : Bool) : (p || (q && r)) = ((p || q) && (p || r)) := by
  smt_translate
  smt

example (p q : Bool) : !(p && q) = (!p || !q) := by
  smt_translate
  smt

example (p q : Bool) : !(p || q) = (!p && !q) := by
  smt_translate
  smt

example (p q : Bool) : (p && q) = (q && p) := by
  smt_translate
  smt

example (p q : Bool) : (p || q) = (q || p) := by
  smt_translate
  smt

example (p q r : Bool) : (p && (q && r)) = ((p && q) && r) := by
  smt_translate
  smt

example (p q r : Bool) : (p || (q || r)) = ((p || q) || r) := by
  smt_translate
  smt

example (p q r : Bool) : (p && (q || r)) = ((p && q) || (p && r)) := by
  smt_translate
  smt

example (p q r : Bool) : (p || (q && r)) = ((p || q) && (p || r)) := by
  smt_translate
  smt

example (p : Bool) : (p && true) = p := by
  smt_translate
  smt

example (p : Bool) : (p || false) = p := by
  smt_translate
  smt

example (p : Bool) : (p && false) = false := by
  smt_translate
  smt

example (p : Bool) : (p || true) = true := by
  smt_translate
  smt

example (p q : Bool) : !(p && q) = (!p || !q) := by
  smt_translate
  smt

example (p q : Bool) : !(p || q) = (!p && !q) := by
  smt_translate
  smt

-- Natural number tests

example (x y z : Nat) (h : x + y ≥ z) (h2 : y + x ≥ z) : x + y - z = y + x - z := by
  smt_translate
  smt

example (x y z w : Nat) (h : x + y + z ≥ w) (h2 : x + z + y ≥ w) : x + y + z - w ≤ x + z + y - w := by
  smt_translate
  smt

example (x y z w : Nat) (h : x * y + z ≥ w) (h2 : z + y * x ≥ w) : x * y + z - w ≥ z + y * x - w := by
  smt_translate
  smt

example (x y : Nat) : x + y = y + x := by
  smt_translate
  smt

example (x y : Nat) : x * y = y * x := by
  smt_translate
  smt

example (x y z : Nat) : x / y + z = z + x / y := by
  smt_translate
  smt

example (x y : Nat) (h : x ≤ y) : x - y = 0 := by
  smt_translate
  smt [*]

example (a b c d : Nat) (h1 : a > 0) (h2 : b > 0) (h3 : c > 0) (h4 : d > 0)
  (h5 : a + b + c + d = 10) : a * b + b * c + c * d + d * a < 100 := by
  smt_translate
  smt [*]

example (x : Nat) : x + 0 = x := by
  smt_translate
  smt

example (x : Nat) : x * 1 = x := by
  smt_translate
  smt

example (x : Nat) : x - x = 0 := by
  smt_translate
  smt

example (x : Nat) : x / 1 = x := by
  smt_translate
  smt

example (x y : Nat) : x + y - y = x := by
  smt_translate
  smt [*]

example (x y : Nat) : x - y ≥ 0 := by
  smt_translate
  smt

example (x : Nat) : x - 1 ≥ 0 := by
  smt_translate
  smt

example (x : Nat) : x * 0 = 0 := by
  smt_translate
  smt

example (x : Nat) : x + x = 2 * x := by
  smt_translate
  smt

example (x y : Nat) : x * (y + 1) = x * y + x := by
  smt_translate
  smt

example (x y : Nat) : x ≤ x + y := by
  smt_translate
  smt [*]

example (x y : Nat) : x * y ≥ 0 := by
  smt_translate
  smt [*]

example (x y : Nat) : x + y ≥ x := by
  smt_translate
  smt [*]

example (x y : Nat) : x + y ≥ y := by
  smt_translate
  smt [*]

example (x : Nat) : x * x ≥ 0 := by
  smt_translate
  smt

-- Rational number tests

example (x y : Rat) : x + y = y + x := by
  smt_translate
  smt

example (x y : Rat) : x * y = y * x := by
  smt_translate
  smt

example (x y : Rat) (h : y ≠ 0) : x * y + 1 ≥ y * x - 1 := by
  smt_translate
  smt [h]

example (ε : Rat) (h1 : ε > 0) : ε / (5 / 2) + ε / 3 + ε / 7 < ε := by
  smt_translate
  smt [h1]

example (x : Rat) : x + 0 = x := by
  smt_translate
  smt

example (x : Rat) : x * 1 = x := by
  smt_translate
  smt

example (x : Rat) : x - x = 0 := by
  smt_translate
  smt

example (x : Rat) : x / 1 = x := by
  smt_translate
  smt

example (x y : Rat) : x + y - y = x := by
  smt_translate
  smt

example (x : Rat) : x * 0 = 0 := by
  smt_translate
  smt

example (x : Rat) : x + x = 2 * x := by
  smt_translate
  smt

example (x y : Rat) : x * (y + 1) = x * y + x := by
  smt_translate
  smt

-- Mixed-type embedding tests (Bool, Nat, Rat)

example (x y : Nat) (p q : Bool) (r s : Rat) (h1 : p && q)
  (h2 : x + y = 10) (h3 : r + s = 5) :
  (p && q) ∧ (r + s = 5) ∧ (x + y = 10) := by
  smt_translate
  smt [*]

example (p q : Bool) (h1 : p && q) : (p || q) := by
  smt_translate
  smt [*]

example (x : Nat) (h : x ≥ x) (h2 : x - x ≥ 0) : x - x - 0 = 0 := by
  smt_translate
  smt

example (x : Nat) (h : x ≥ x + 1) : x - (x + 1) = 0 := by
  smt_translate
  smt [*]

example (x : Int) (h : x ≥ 0) : x - x = 0 := by
  smt [*]

example (a b : Rat) (x y : Nat) (p q : Bool) (h1 : a ≠ b) (h2 : x > y) (h3 : p || q) :
  (a ≠ b) ∧ (x > y) ∧ (p || q) ∧ (y - x = 0) := by
  smt_translate
  smt [*]

-- Quantifier tests over Nat (∀, ∃, predicates)

example : ∀ (x y : Nat), x - y ≥ 0 := by
  smt_translate
  smt [*]

example (x y : Nat) : x - y ≥ 0 := by
  smt_translate
  smt [*]

example : ∃ (x y : Nat), x - y ≥ 0 := by
  smt_translate
  smt [*]

example : 4 + 5 = 9 := by
  smt_translate
  smt [*]

example : ∀ x : Nat, x + x ≥ 0 := by
  smt_translate
  smt [*]

example : ∃ x : Nat, x = 0 := by
  smt_translate
  smt [*]

example (p : Nat → Prop) (w : Nat) (h : p w) : ∃ x, p x := by
  smt_translate
  smt [*]

example (p : Nat → Prop) (h : ∃ x, p x) : ∃ y, p y := by
  smt_translate
  smt [*]

example (p : Nat → Prop) (w : Nat) (h : p w) : ∃ x, p x ∨ p x := by
  smt_translate
  smt [*]

example (f : Nat → Nat) : ∃ n, f n ≥ n := by
  smt_translate
  smt [*]

example (p : Nat → Prop) (w : Nat) (z : Nat) (h : p w ∨ p z) : ∃ x, p x := by
  smt_translate
  smt [*]

example (f : Nat → Nat) : ∀ n, f n ≥ 0 := by
  smt_translate
  smt [*]

example (p : Nat → Prop) (w : Nat) (h : p w) : ∃ x, p x ∨ p x := by
  smt_translate
  smt [*]

example (p : Nat → Prop) (w : Nat) (h : p w) : ∃ x, x ≥ 0 ∧ p x := by
  smt_translate
  smt [*]

example (p : Nat → Prop) (h : ∃ x, p x) : ∃ y, p y := by
  smt_translate
  smt [*]

example : True ∨ ∀ x : Nat, x ≥ 0 := by
  smt_translate
  smt [*]
