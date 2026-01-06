import Smt
import Smt.Real
import Smt.Preprocess.Embedding

namespace Smt.Preprocess.Tactic

syntax (name := embeddingTac) "embedding " ("[" term,* "]")? : tactic

open Lean Elab Tactic in
@[tactic embeddingTac] def evalEmbedding : Tactic
  | `(tactic| embedding [$hs,*]) => withMainContext do
    let mv ← getMainGoal
    let hs ← hs.getElems.mapM (Term.elabTerm · none)
    Lean.logInfo m!"Before: {hs}"
    let ⟨map, hs, mv⟩ ← Smt.Preprocess.embedding mv hs
    mv.withContext (Lean.logInfo m!"After: {hs}")
    mv.withContext (Lean.logInfo m!"Map: {map.toList}")
    (Lean.logInfo m!"Map: {map.toList}")
    replaceMainGoal [mv]
  | `(tactic| embedding) => withMainContext do
    let mv ← getMainGoal
    let ⟨map, _, mv⟩ ← Smt.Preprocess.embedding mv #[]
    mv.withContext (Lean.logInfo m!"Map: {map.toList}")
    (Lean.logInfo m!"Map: {map.toList}")
    replaceMainGoal [mv]
  | _ => throwUnsupportedSyntax

end Smt.Preprocess.Tactic

-- Boolean tests

example (p q : Bool) (h : p && q) (h2 : p || q) : (1 : Int) + 1 = 2 := by
  smt

example (p q : Bool) : (p || q) || (!p && !q) := by
  smt

example (p : Bool) : (p || !p) = true := by
  smt

example (p : Bool) : (p && !p) = false := by
  smt

example (p q r : Bool) : (p && (q || r)) = ((p && q) || (p && r)) := by
  smt

example (p q r : Bool) : (p || (q && r)) = ((p || q) && (p || r)) := by
  smt

example (p q : Bool) : !(p && q) = (!p || !q) := by
  smt

example (p q : Bool) : !(p || q) = (!p && !q) := by
  smt

example (p q : Bool) : (p && q) = (q && p) := by
  smt

example (p q : Bool) : (p || q) = (q || p) := by
  smt

example (p q r : Bool) : (p && (q && r)) = ((p && q) && r) := by
  smt

example (p q r : Bool) : (p || (q || r)) = ((p || q) || r) := by
  smt

example (p q r : Bool) : (p && (q || r)) = ((p && q) || (p && r)) := by
  smt

example (p q r : Bool) : (p || (q && r)) = ((p || q) && (p || r)) := by
  smt

example (p : Bool) : (p && true) = p := by
  smt

example (p : Bool) : (p || false) = p := by
  smt

example (p : Bool) : (p && false) = false := by
  smt

example (p : Bool) : (p || true) = true := by
  smt

example (p q : Bool) : !(p && q) = (!p || !q) := by
  smt

example (p q : Bool) : !(p || q) = (!p && !q) := by
  smt

-- Natural number tests

example (x y z : Nat) : x + y - z = y + x - z := by
  smt

example : ∀ (x y z : Nat), x + y - z = y + x - z := by
  smt

example (x y z w : Nat) : x + y + z - w ≤ x + z + y - w := by
  smt

example (x y z w : Nat) : x * y + z - w ≥ z + y * x - w := by
  smt

example (x y : Nat) : x + y = y + x := by
  smt

example (x y : Nat) : x * y = y * x := by
  smt

example (x y z : Nat) : x / y + z = z + x / y := by
  smt

example (x y : Nat) (h : x ≤ y) : x - y = 0 := by
  smt [h]

example (a b c d : Nat) (h1 : a > 0) (h2 : b > 0) (h3 : c > 0) (h4 : d > 0)
  (h5 : a + b + c + d = 10) : a * b + b * c + c * d + d * a < 100 := by
  smt? [*]

example (x : Nat) : x + 0 = x := by
  smt

example (x : Nat) : x * 1 = x := by
  smt

example (x : Nat) : x - x = 0 := by
  smt

example (x : Nat) : x / 1 = x := by
  smt

example (x y : Nat) : x + y - y = x := by
  smt

example (x y : Nat) : x - y ≥ 0 := by
  smt

example (x : Nat) : x - 1 ≥ 0 := by
  smt

example (x : Nat) : x * 0 = 0 := by
  smt

example (x : Nat) : x + x = 2 * x := by
  smt

example (x y : Nat) : x * (y + 1) = x * y + x := by
  smt

example (x y : Nat) : x ≤ x + y := by
  smt

example (x y : Nat) : x * y ≥ 0 := by
  smt

example (x y : Nat) : x + y ≥ x := by
  smt

example (x y : Nat) : x + y ≥ y := by
  smt

example (x : Nat) : x * x ≥ 0 := by
  smt

example : ∀ n : Nat, ∀ m : Int, n = m → n ≥ 0 := by
  smt

example {f : Int → Nat} : ∀ m : Int, f m = m → m ≥ 0 := by
  smt

example {f : Nat → Int} : ∀ m : Nat, f m = m → m ≥ 0 := by
  smt

example {f : Nat → Nat → Int} : ∀ m : Nat, f m m = m → m ≥ 0 := by
  smt

example {f : Nat → Int → Nat} : ∀ m : Int, m ≥ 0 → f m.toNat 0 = m → m ≥ 0 := by
  smt

example {f : Nat → Int → Nat → Nat} : ∀ m : Int, m ≥ 0 → f m.toNat 5 0 = m → m ≥ 0 := by
  smt

-- Rational number tests

example (x y : Rat) : x + y = y + x := by
  smt

example (x y : Rat) : x * y = y * x := by
  revert x y
  smt

example (x y : Rat) (h : y ≠ 0) : x * y + 1 ≥ y * x - 1 := by
  smt [h]

example (ε : Rat) (h1 : ε > 0) : ε / (5 / 2) + ε / 3 + ε / 7 < ε := by
  smt [h1]

example (x : Rat) : x + 0 = x := by
  smt

example (x : Rat) : x * 1 = x := by
  smt

example (x : Rat) : x - x = 0 := by
  smt

example (x : Rat) : x / 1 = x := by
  smt

example (x y : Rat) : x + y - y = x := by
  smt

example (x : Rat) : x * 0 = 0 := by
  smt

example (x : Rat) : x + x = 2 * x := by
  smt

example (x y : Rat) : x * (y + 1) = x * y + x := by
  smt

-- Mixed-type embedding tests (Bool, Nat, Rat)

example (x y : Nat) (p q : Bool) (r s : Rat) (h1 : p && q)
  (h2 : x + y = 10) (h3 : r + s = 5) :
  (p && q) ∧ (r + s = 5) ∧ (x + y = 10) := by
  smt [*]

example (x : Nat) (h : x ≥ x) (h2 : x - x ≥ 0) : x - x - 0 = 0 := by
  smt [*]

example (x : Nat) (h : x ≥ x + 1) : x - (x + 1) = 0 := by
  smt [h]

example (x : Int) (h : x ≥ 0) : x - x = 0 := by
  smt [*]

example (a b : Rat) (x y : Nat) (p q : Bool) (h1 : a ≠ b) (h2 : x > y) (h3 : p || q) :
  (a ≠ b) ∧ (x > y) ∧ (p || q) ∧ (y - x = 0) := by
  smt [*]

-- Quantifier tests over Bool (∀, ∃, predicates)

example : ∀ (x y : Bool), (x && y) == false || (x && y) == true := by
  smt [*]

example (x y : Bool) : (x && y) == false || (x && y) == true := by
  smt [*]

example : ∃ (x y : Bool), (x && y) == false || (x && y) == true := by
  smt [*]

example : (true || false) == true := by
  smt [*]

example : ∀ x : Bool, (x || x) == true || (x || x) == false := by
  smt [*]

example : ∃ x : Bool, (x || x) == true || (x || x) == false := by
  smt [*]

example (p : Bool → Prop) (w : Bool) (h : p w) : ∃ x, p x := by
  smt [*]

example (p : Bool → Prop) (h : ∃ x, p x) : ∃ y, p y := by
  smt [*]

example (p : Bool → Prop) (w : Bool) (h : p w) : ∃ x, p x ∨ p x := by
  smt [*]

example {f : Bool → Bool → Bool} {x y} {h : x = y} : f x y = f y x := by
  smt [h]

example (f : Bool → Bool) : ∃ n, f n == false || f n == true := by
  smt [*]

example (f : Bool → Bool → Bool) : ∃ x n, f x n == false || f x n == true := by
  smt [*]

example (p : Bool → Prop) (w : Bool) (z : Bool) (h : p w ∨ p z) : ∃ x, p x := by
  smt [*]

example (f : Bool → Bool) : ∀ n, f n == false || f n == true := by
  smt [*]

example (p : Bool → Prop) (w : Bool) (h : p w) : ∃ x, p x ∨ p x := by
  smt [*]

example (p : Bool → Prop) (w : Bool) (h : p w) : ∃ x, (x == true || x == false) ∧ p x := by
  smt [*]

example (p : Bool → Prop) (h : ∃ x, p x) : ∃ y, p y := by
  smt [*]

example : true ∨ ∀ x : Bool, (x == true || x == false) := by
  smt [*]

-- Quantifier tests over Rat (∀, ∃, predicates)

example : ∀ (x y : Rat), x - y ≥ 0 ∨ x - y < 0 := by
  smt [*]

example (x y : Rat) : x - y ≥ 0 ∨ x - y < 0 := by
  smt [*]

example : ∃ (x y : Rat), x - y ≥ 0 := by
  smt [*]

example : (4 : Rat) + 5 = 9 := by
  smt [*]

example : ∀ x : Rat, x * x ≥ 0 := by
  smt [*]

example : ∃ x : Rat, x = 0 := by
  embedding
  smt +showQuery [*]

example (p : Nat → Prop) (w : Nat) (h : p w) : ∃ x, p x := by
  smt [*]

example (p : Nat → Prop) (h : ∃ x, p x) : ∃ y, p y := by
  smt [*]

example (p : Nat → Prop) (w : Nat) (h : p w) : ∃ x, p x ∨ p x := by
  smt [*]

example {f : Rat → Nat → Rat} {x y} {h : x = ↑y} : f x y = f x y := by
  smt

example (f : Rat → Rat) : ∃ n, f n ≥ n := by
  smt +showQuery [*]

example (f : Int → Rat → Rat) : ∃ x n, f x n ≥ n := by
  smt +showQuery [*]

example : ∀ x : Nat, ∀ y : Int, ↑x = y → y.toNat >= 0 := by
  smt

example (p : Rat → Prop) (w : Rat) (z : Rat) (h : p w ∨ p z) : ∃ x, p x := by
  smt [*]

example (f : Rat → Rat) : ∀ n, f n ≥ 0 ∨ f n < 0 := by
  smt [*]

example (p : Rat → Prop) (w : Rat) (h : p w) : ∃ x, p x ∨ p x := by
  smt [*]

example (p : Rat → Prop) (w : Rat) (h : p w) : ∃ x, x ≥ 0 ∧ p x := by
  smt +showQuery [*]

example (p : Rat → Prop) (h : ∃ x, p x) : ∃ y, p y := by
  smt [*]

example {f : Rat → Int → Rat} {x y} {h : ↑y = x} {h' : f x y ≠ f y ⌊x⌋} : False := by
  revert f x y
  simp only [embedding]
  -- smt [h']

example {f : Rat → Int → Rat} {x y} {h : x = ↑y} {h' : f x y ≠ f x y} : False := by
  smt [*]

example {x : Nat} : x + 3 = 3 + x := by
  smt

private theorem ite_infinite_simp_recursion (node : Type) [DecidableEq node] [Nonempty node]
  (n : node) (f : node → Bool)
  (h : ∀ (a : node), f a = if n = a then true else true) :
  ∀ N M, f N = true → f M = true → N = N := by
  smt [h]

private theorem ite_simplification (node : Type) [node_dec_eq : DecidableEq node] [Nonempty node] (sender n next : node)
  (st_leader : node → Bool) (st_pending : node → node → Bool)
  (st'_leader : node → Bool) (st'_pending : node → node → Bool)
  (h : ∀ (a a_1 : node), st'_pending a a_1 = if sender = a ∧ n = a_1 then x else st_pending a a_1) :
  ∀ N M, st'_leader N = true → st'_leader M = true → N = N := by
  smt [h]

private theorem more_complex (node : Type) [node_dec_eq : DecidableEq node] (sender n next : node)
  (tot_le : node → node → Prop) (tot_le_refl : ∀ (x : node), tot_le x x)
  (tot_le_trans : ∀ (x y z : node), tot_le x y → tot_le y z → tot_le x z)
  (tot_le_antisymm : ∀ (x y : node), tot_le x y → tot_le y x → x = y)
  (tot_le_total : ∀ (x y : node), tot_le x y ∨ tot_le y x) (btwn_btw : node → node → node → Prop)
  (btwn_btw_ring : ∀ (x y z : node), btwn_btw x y z → btwn_btw y z x)
  (btwn_btw_trans : ∀ (w x y z : node), btwn_btw w x y → btwn_btw w y z → btwn_btw w x z)
  (btwn_btw_side : ∀ (w x y : node), btwn_btw w x y → ¬btwn_btw w y x)
  (btwn_btw_total : ∀ (w x y : node), btwn_btw w x y ∨ btwn_btw w y x ∨ w = x ∨ w = y ∨ x = y) (h : sender = n)
  (a_left : ∀ (Z : node), ¬n = next ∧ (¬Z = n → ¬Z = next → btwn_btw n next Z)) (x : Bool) (st_leader : node → Bool)
  (hinv_right_left : ∀ (L N : node), st_leader L = true → tot_le N L)
  (hinv_left : ∀ (N M : node), st_leader N = true → st_leader M = true → N = M) (st_pending : node → node → Bool)
  (hinv_right_right_right : ∀ (L N : node), st_pending L L = true → tot_le N L)
  (hinv_right_right_left : ∀ (S D N : node), st_pending S D = true → btwn_btw S N D → tot_le N S)
  (a_right_left : st_pending sender n = true) (st'_leader : node → Bool) (st'_pending : node → node → Bool)
  (a_right_right_1_1_left_left : ∀ (a : node), st'_leader a = if n = a then true else st_leader a)
  (a_right_right_1_1_left_right :
    ∀ (a a_1 : node), st'_pending a a_1 = if sender = a ∧ n = a_1 then x else st_pending a a_1)
  (h : sender = n)
  (N M : node) : st'_leader N = true → st'_leader M = true → N = M := by
  smt (config := { extraSolverOptions := [("finite-model-find", "true")] })
  [hinv_left, h, a_right_left, a_right_right_1_1_left_left, a_right_right_1_1_left_right,
    tot_le_refl, tot_le_trans, tot_le_antisymm, tot_le_total, hinv_right_left,
    hinv_right_right_right, btwn_btw_ring, btwn_btw_trans, btwn_btw_side, btwn_btw_total,
    a_left, hinv_right_right_left]
