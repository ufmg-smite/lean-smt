import Smt

-- example : ∃ (x : Int), x * x = 2 := by
--   smt

example : p ∧ q → p := by
  smt

example (a b : Int) : b < 0 → a > 0 → b * (- 2)  * a * b* b * (- 3) * a * a < 0 := by
  smt
  all_goals sorry

example (a b : Int) (hb : b < 0) (ha : a < 0) : b * (- 2)  * a *  b * (- 3) * a * a < 0 := by
  smt [hb, ha]
  all_goals sorry

-- example (m n : Int) (h : m > 0) : n % m < m := by
--   smt [h]
--   all_goals sorry

example {x y : Int} {f : Int → Int} : ¬(x ≤ y ∧ y ≤ x ∧ ¬f x = f y) := by
  smt
  all_goals sorry

example {p q r : Prop} (hp : ¬p) (hq : ¬q) (hr : r) : ¬(p ∨ q ∨ ¬r) := by
  smt [hp, hq, hr]

example {p q r : Prop} : ((p ∧ q) ∧ r) = (r ∧ True ∧ q ∧ p ∧ p) := by
  smt

example {p q r : Prop} : ((p ∧ q) ∧ r) = (r ∧ True ∧ q ∧ p ∧ p) := by
  ac_rfl

example {a b : Int} (h : a < b) (w : b < a) : False := by
  smt [h, w]
  all_goals sorry

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
  all_goals sorry

example (e b c a v0 v1 : Int) (h1 : v0 = 5*a) (h2 : v1 = 3*b)
    (h3 : v0 + v1 + c = 10) : v0 + 5 + (v1 - 3) + (c - 2) = 10 := by
  smt [h1, h2, h3]
  all_goals sorry

example (h : (1 : Int) < 0) (g : ¬ (37 : Int) < 42) (_k : True) (l : (-7 : Int) < 5): (3 : Int) < 7 := by
  smt [h, g, _k, l]
  all_goals sorry

example (u v r s t : Int) (h : 0 < u*(t*v + t*r + s)) : 0 < (t*(r + v) + s)*3*u := by
  smt [h]
  all_goals sorry

example (A B : Int) (h : 0 < 3 * A * B) : 0 < 8*A*B := by
  smt [h]
  all_goals sorry

example (A B : Int) (h : 0 < 8 * A * B) : 0 < A*B := by
  smt [h]
  all_goals sorry

example (A B : Int) (h : 0 < A * B) : 0 < A*8*B := by
  smt [h]
  all_goals sorry

example (x : Int) : 0 ≤ x := by
  have h : 0 ≤ x := sorry
  smt [h]

example (u v r s t : Int) (h : 0 < u*(t*v + t*r + s)) :
    0 < (t*(r + v) + s)*3*u := by
  smt [h]
  all_goals sorry

example (A B : Int) (h : 0 < A * B) : 0 < 8*A*B := by
  smt [h]
  all_goals sorry

example (x y z : Int) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0) (h3 : 12*y - 4* z < 0) : False := by
  smt [h1, h2, h3]
  all_goals sorry

example (x y z : Int) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0) (h3 : x*y < 5) (h3 : 12*y - 4* z < 0) :
    False := by
  smt [h1, h2, h3]
  all_goals sorry

example (prime : Int → Prop) (w x y z : Int) (h1 : 4*x + (-3)*y + 6*w ≤ 0) (h2 : (-1)*x < 0) (h3 : y < 0) (h4 : w ≥ 0)
    (h5 : prime x) : False := by
  smt [h1, h2, h3, h4]
  all_goals sorry

-- set_option maxRecDepth 2000000

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
  all_goals sorry
