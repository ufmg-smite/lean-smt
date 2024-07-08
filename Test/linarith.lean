import Smt
import Smt.Real

example {x y : Real} {f : Real → Real} : ¬(((1/2 : Real) = 1/2) ∧ x ≤ y ∧ y ≤ x ∧ ¬f x = f y) := by
  smt

example {x y : Real} {f : Real → Real} : ¬(((1/2 : Int) = 1/2) ∧ x ≤ y ∧ y ≤ x ∧ ¬f x = f y) := by
  smt

example {x y : Int} {f : Int → Int} : ¬(x ≤ y ∧ y ≤ x ∧ ¬f x = f y) := by
  smt

example {p q r : Prop} (hp : ¬p) (hq : ¬q) (hr : r) : ¬(p ∨ q ∨ ¬r) := by
  smt [hp, hq, hr]

example {p q r : Prop} : ((p ∧ q) ∧ r) = (r ∧ True ∧ q ∧ p ∧ p) := by
  smt

example {a b : Int} (h : a < b) (w : b < a) : False := by
  smt [h, w]

example
    {a b c : Int}
    (ha : a < 0)
    (hb : ¬b = 0)
    (hc' : c = 0)
    (h₁ : (1 - a) * (b * b) ≤ 0)
    (hc : (0 : Int) ≤ 0)
    (w : -(a * -b * -b + b * -b + 0) = (1 - a) * (b * b))
    (h₂ : (1 - a) * (b * b) ≤ 0) :
    0 < 1 - a := by
  smt [ha, hb, hc', h₁, hc, w, h₂]

example (e b c a v0 v1 : Int) (h1 : v0 = 5*a) (h2 : v1 = 3*b)
    (h3 : v0 + v1 + c = 10) : v0 + 5 + (v1 - 3) + (c - 2) = 10 := by
  smt [h1, h2, h3]

example (h : (1 : ℤ) < 0) (g : ¬ (37 : ℤ) < 42) (_k : True) (l : (-7 : ℤ) < 5): (3 : ℤ) < 7 := by
  smt [h, g, _k, l]

example (u v r s t : Int) (h : 0 < u*(t*v + t*r + s)) : 0 < (t*(r + v) + s)*3*u := by
  smt [h]

example (A B : Int) (h : 0 < 3 * A * B) : 0 < 8*A*B := by
  smt [h]

example (A B : Int) (h : 0 < 8 * A * B) : 0 < A*B := by
  smt [h]

example (A B : Int) (h : 0 < A * B) : 0 < A*8*B := by
  smt [h]

example (x : Int) : 0 ≤ x := by
  have h : 0 ≤ x := sorry
  smt [h]

example (u v r s t : Int) (h : 0 < u*(t*v + t*r + s)) :
    0 < (t*(r + v) + s)*3*u := by
  smt [h]

example (A B : Int) (h : 0 < A * B) : 0 < 8*A*B := by
  smt [h]

example (A B : Real) (h : 0 < A * B) : 0 < A*B/8 := by
  smt [h]

example (A B : Real) (h : 0 < A * B) : 0 < A/8*B := by
  smt [h]

example (ε : Real) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε := by
  smt [h1]

example (x y z : Real) (h1 : 2*x < 3*y) (h2 : -4*x + z/2 < 0)
        (h3 : 12*y - z < 0)  : False := by
  smt [h1, h2, h3]

example (ε : Real) (h1 : ε > 0) : ε / 2 < ε := by
  smt [h1]

example (ε : Real) (h1 : ε > 0) : ε / 3 + ε / 3 + ε / 3 = ε := by
  smt [h1]

example (x : Real) (h : 0 < x) : 0 < x/1 := by
  smt [h]

example (x : Real) (h : x < 0) : 0 < x/(-1) := by
  smt [h]

example (x : Real) (h : x < 0) : 0 < x/(-2) := by
  smt [h]

example (x : Real) (h : x < 0) : 0 < x/(-4/5) := by
  smt [h]

example (x : Real) (h : 0 < x) : 0 < x/2/3 := by
  smt [h]

example (x : Real) (h : 0 < x) : 0 < x/(2/3) := by
  smt [h]

example (a b c : Real) (h2 : b + 2 > 3 + b) : False := by
  smt [h2]
  all_goals (ring_nf; simp)
  norm_num

example (a b c : Real) (h2 : b + 2 > 3 + b) : False := by
  smt [h2]
  all_goals (ring_nf; simp)
  norm_num

example (g v V c h : Real) (h1 : h = 0) (h2 : v = V) (h3 : V > 0) (h4 : g > 0)
    (h5 : 0 ≤ c) (h6 : c < 1) : v ≤ V := by
  smt [h1, h2, h3, h4, h5, h6]

example (x y z : ℤ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0) (h3 : 12*y - 4* z < 0) : False := by
  smt [h1, h2, h3]

example (x y z : ℤ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0) (h3 : x*y < 5) (h3 : 12*y - 4* z < 0) :
    False := by
  smt [h1, h2, h3]

example (a b c : Real) (h1 : a > 0) (h2 : b > 5) (h3 : c < -10) (h4 : a + b - c < 3) : False := by
  smt [h1, h2, h3, h4]

example (a b c : Real) (h2 : b > 0) (h3 : ¬ b ≥ 0) : False := by
  smt [h2, h3]

example (x y z : Real) (hx : x ≤ 3*y) (h2 : y ≤ 2*z) (h3 : x ≥ 6*z) : x = 3*y := by
  smt [hx, h2, h3]

example (x y z : ℤ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0) (h3 : x*y < 5) : ¬ 12*y - 4* z < 0 := by
  smt [h1, h2, h3]

example (x y z : Real) (hx : ¬ x > 3*y) (h2 : ¬ y > 2*z) (h3 : x ≥ 6*z) : x = 3*y := by
  smt [hx, h2, h3]

-- example (x y : Real) (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3) (h' : (x + 4) * x ≥ 0)
--     (h'' : (6 + 3 * y) * y ≥ 0) : False := by
--   smt [h, h'']
--   all_goals sorry

example (a : Real) (ha : 0 ≤ a) : 0 * 0 ≤ 2 * a := by
  smt [ha]

example (x y : Real) (h : x < y) : x ≠ y := by
  smt [h]

-- example (x y : Real) (h : x < y) : ¬ x = y := by
--   smt [h]

-- example (x : Real) : id x ≥ x := by
--   let idℝ := fun (x : Real) => x
--   let hidℝ : idℝ = fun x => x := rfl
--   have : @id Real = idℝ := rfl
--   rewrite [this]
--   smt [idℝ]
--   all_goals (ring_nf; simp)
--   sorry

example (prime : ℤ → Prop) (x y z : Real) (h1 : 2*x + ((-3)*y) < 0) (h2 : (-4)*x + 2*z < 0) (h3 : 12*y + (-4)* z < 0)
    (h4 : prime 7) : False := by
  smt [h1, h2, h3, h4]

example (prime : ℤ → Prop) (x y z : Real) (h1 : 2*1*x + (3)*(y*(-1)) < 0) (h2 : (-2)*x*2 < -(z + z))
    (h3 : 12*y + (-4)* z < 0) (h4 : prime 7) : False := by
  smt [h1, h2, h3, h4]

example (prime : ℤ → Prop) (w x y z : ℤ) (h1 : 4*x + (-3)*y + 6*w ≤ 0) (h2 : (-1)*x < 0) (h3 : y < 0) (h4 : w ≥ 0)
    (h5 : prime x) : False := by
  smt [h1, h2, h3, h4]

set_option maxRecDepth 200000 in
example (u v x y A B : Int)
(a : 0 < A)
(a_1 : 0 <= 1 - A)
(a_2 : 0 <= B - 1)
(a_3 : 0 <= B - x)
(a_4 : 0 <= B - y)
(a_5 : 0 <= u)
(a_6 : 0 <= v)
(a_7 : 0 < A - u)
(a_8 : 0 < A - v) :
 (0 < A * A)
-> (0 <= A * (1 - A))
-> (0 <= A * (B - 1))
-> (0 <= A * (B - x))
-> (0 <= A * (B - y))
-> (0 <= A * u)
-> (0 <= A * v)
-> (0 < A * (A - u))
-> (0 < A * (A - v))
-> (0 <= (1 - A) * A)
-> (0 <= (1 - A) * (1 - A))
-> (0 <= (1 - A) * (B - 1))
-> (0 <= (1 - A) * (B - x))
-> (0 <= (1 - A) * (B - y))
-> (0 <= (1 - A) * u)
-> (0 <= (1 - A) * v)
-> (0 <= (1 - A) * (A - u))
-> (0 <= (1 - A) * (A - v))
-> (0 <= (B - 1) * A)
-> (0 <= (B - 1) * (1 - A))
-> (0 <= (B - 1) * (B - 1))
-> (0 <= (B - 1) * (B - x))
-> (0 <= (B - 1) * (B - y))
-> (0 <= (B - 1) * u)
-> (0 <= (B - 1) * v)
-> (0 <= (B - 1) * (A - u))
-> (0 <= (B - 1) * (A - v))
-> (0 <= (B - x) * A)
-> (0 <= (B - x) * (1 - A))
-> (0 <= (B - x) * (B - 1))
-> (0 <= (B - x) * (B - x))
-> (0 <= (B - x) * (B - y))
-> (0 <= (B - x) * u)
-> (0 <= (B - x) * v)
-> (0 <= (B - x) * (A - u))
-> (0 <= (B - x) * (A - v))
-> (0 <= (B - y) * A)
-> (0 <= (B - y) * (1 - A))
-> (0 <= (B - y) * (B - 1))
-> (0 <= (B - y) * (B - x))
-> (0 <= (B - y) * (B - y))
-> (0 <= (B - y) * u)
-> (0 <= (B - y) * v)
-> (0 <= (B - y) * (A - u))
-> (0 <= (B - y) * (A - v))
-> (0 <= u * A)
-> (0 <= u * (1 - A))
-> (0 <= u * (B - 1))
-> (0 <= u * (B - x))
-> (0 <= u * (B - y))
-> (0 <= u * u)
-> (0 <= u * v)
-> (0 <= u * (A - u))
-> (0 <= u * (A - v))
-> (0 <= v * A)
-> (0 <= v * (1 - A))
-> (0 <= v * (B - 1))
-> (0 <= v * (B - x))
-> (0 <= v * (B - y))
-> (0 <= v * u)
-> (0 <= v * v)
-> (0 <= v * (A - u))
-> (0 <= v * (A - v))
-> (0 < (A - u) * A)
-> (0 <= (A - u) * (1 - A))
-> (0 <= (A - u) * (B - 1))
-> (0 <= (A - u) * (B - x))
-> (0 <= (A - u) * (B - y))
-> (0 <= (A - u) * u)
-> (0 <= (A - u) * v)
-> (0 < (A - u) * (A - u))
-> (0 < (A - u) * (A - v))
-> (0 < (A - v) * A)
-> (0 <= (A - v) * (1 - A))
-> (0 <= (A - v) * (B - 1))
-> (0 <= (A - v) * (B - x))
-> (0 <= (A - v) * (B - y))
-> (0 <= (A - v) * u)
-> (0 <= (A - v) * v)
-> (0 < (A - v) * (A - u))
-> (0 < (A - v) * (A - v))
->
 u * y + v * x + u * v < 3 * A * B := by
  smt [a, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8]
