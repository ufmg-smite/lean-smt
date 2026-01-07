import Smt

namespace Smt.Preprocess.Tactic

syntax (name := smtNormalize) "smt_normalize " ("[" term,* "]")? : tactic

open Lean Elab Tactic in
@[tactic smtNormalize] def evalSmtNormalize : Tactic.Tactic
  | `(tactic| smt_normalize [$hs,*]) => Lean.Elab.Tactic.withMainContext do
    let mv ← getMainGoal
    let hs ← hs.getElems.mapM (Term.elabTerm · none)
    Lean.logInfo m!"Before: {hs}"
    let ⟨map, hs, mv⟩ ← Smt.Preprocess.normalize mv hs
    mv.withContext (Lean.logInfo m!"After: {hs}")
    mv.withContext (Lean.logInfo m!"Map: {map.toList}")
    (Lean.logInfo m!"Map: {map.toList}")
    replaceMainGoal [mv]
  | `(tactic| smt_normalize) => withMainContext do
    let mv ← getMainGoal
    let ⟨map, _, mv⟩ ← Smt.Preprocess.normalize mv #[]
    mv.withContext (Lean.logInfo m!"Map: {map.toList}")
    (Lean.logInfo m!"Map: {map.toList}")
    replaceMainGoal [mv]
  | _ => throwUnsupportedSyntax

end Smt.Preprocess.Tactic

example (p : Prop) : p ↔ p := by
  smt_normalize
  smt

example (p q : Prop) (h : p ↔ q) : p = q := by
  smt_normalize
  smt [*]

example (p q : Prop) (h : p ↔ q) : p = q := by
  smt_normalize [h]
  smt [*]

example : Int.sub x (Int.ofNat 1) = x - 1 := by
  smt

example (x : Int) : Int.add x (Int.ofNat 1) = Int.add (Int.ofNat 1) x := by
  smt

def t (p : Prop) : p ↔ p := by simp

example (p q r : Prop) (ht : True) (hpqr : (p ↔ q) ∧ (q ↔ r)) (ht' : True) : p ↔ r := by
  smt_normalize [hpqr, ht, ht', t]
  smt [*]

-- Boolean tests

example (p q : Bool) (h : p && q) (h2 : p || q) : (1 : Int) + 1 = 2 := by
  smt +mono

example (p q : Bool) : (p || q) || (!p && !q) := by
  smt +mono

example (p : Bool) : (p || !p) = true := by
  smt +mono

example (p : Bool) : (p && !p) = false := by
  smt +mono

example (p q r : Bool) : (p && (q || r)) = ((p && q) || (p && r)) := by
  smt +mono

example (p q r : Bool) : (p || (q && r)) = ((p || q) && (p || r)) := by
  smt +mono

example (p q : Bool) : !(p && q) = (!p || !q) := by
  smt +mono

example (p q : Bool) : !(p || q) = (!p && !q) := by
  smt +mono

example (p q : Bool) : (p && q) = (q && p) := by
  smt +mono

example (p q : Bool) : (p || q) = (q || p) := by
  smt +mono

example (p q r : Bool) : (p && (q && r)) = ((p && q) && r) := by
  smt +mono

example (p q r : Bool) : (p || (q || r)) = ((p || q) || r) := by
  smt +mono

example (p q r : Bool) : (p && (q || r)) = ((p && q) || (p && r)) := by
  smt +mono

example (p q r : Bool) : (p || (q && r)) = ((p || q) && (p || r)) := by
  smt +mono

example (p : Bool) : (p && true) = p := by
  smt +mono

example (p : Bool) : (p || false) = p := by
  smt +mono

example (p : Bool) : (p && false) = false := by
  smt +mono

example (p : Bool) : (p || true) = true := by
  smt +mono

example (p q : Bool) : !(p && q) = (!p || !q) := by
  smt +mono

example (p q : Bool) : !(p || q) = (!p && !q) := by
  smt +mono

-- Natural number tests

example (x y z : Nat) : x + y - z = y + x - z := by
  smt +mono

example : ∀ (x y z : Nat), x + y - z = y + x - z := by
  smt +mono

example (x y z w : Nat) : x + y + z - w ≤ x + z + y - w := by
  smt +mono

example (x y z w : Nat) : x * y + z - w ≥ z + y * x - w := by
  smt +mono

example (x y : Nat) : x + y = y + x := by
  smt +mono

example (x y : Nat) : x * y = y * x := by
  smt +mono

example (x y z : Nat) : x / y + z = z + x / y := by
  smt +mono

example (x y : Nat) (h : x ≤ y) : x - y = 0 := by
  smt +mono [h]

example (x : Nat) : x + 0 = x := by
  smt +mono

example (x : Nat) : x * 1 = x := by
  smt +mono

example (x : Nat) : x - x = 0 := by
  smt +mono

example (x : Nat) : x / 1 = x := by
  smt +mono

example (x y : Nat) : x + y - y = x := by
  smt +mono

example (x y : Nat) : x - y ≥ 0 := by
  smt +mono

example (x : Nat) : x - 1 ≥ 0 := by
  smt +mono

example (x : Nat) : x * 0 = 0 := by
  smt +mono

example (x : Nat) : x + x = 2 * x := by
  smt +mono

example (x y : Nat) : x * (y + 1) = x * y + x := by
  smt +mono

example (x y : Nat) : x ≤ x + y := by
  smt +mono

example (x y : Nat) : x * y ≥ 0 := by
  smt +mono

example (x y : Nat) : x + y ≥ x := by
  smt +mono

example (x y : Nat) : x + y ≥ y := by
  smt +mono

example (x : Nat) : x * x ≥ 0 := by
  smt +mono

example : ∀ n : Nat, ∀ m : Int, n = m → n ≥ 0 := by
  smt +mono

example {f : Int → Nat} : ∀ m : Int, f m = m → m ≥ 0 := by
  smt +mono

example {f : Nat → Int} : ∀ m : Nat, f m = m → m ≥ 0 := by
  smt +mono

example {f : Nat → Nat → Int} : ∀ m : Nat, f m m = m → m ≥ 0 := by
  smt +mono

example {f : Nat → Int → Nat} : ∀ m : Int, m ≥ 0 → f m.toNat 0 = m → m ≥ 0 := by
  smt +mono

example {f : Nat → Int → Nat → Nat} : ∀ m : Int, m ≥ 0 → f m.toNat 5 0 = m → m ≥ 0 := by
  smt +mono

-- Rational number tests

example (x y : Rat) : x + y = y + x := by
  smt +mono [Rat.add_comm]

example (x y : Rat) : x * y = y * x := by
  revert x y
  smt +mono [Rat.mul_comm]

example (x y : Rat) (h : y ≠ 0) : x * y + 1 ≥ y * x - 1 := by
  -- smt +mono [h]
  sorry

example (ε : Rat) (h1 : ε > 0) : ε / (5 / 2) + ε / 3 + ε / 7 < ε := by
  -- smt +mono [h1]
  sorry

example (x : Rat) : x + 0 = x := by
  smt +mono [Rat.add_zero]

example (x : Rat) : x * 1 = x := by
  smt +mono [Rat.mul_one]

example (x : Rat) : x - x = 0 := by
  smt +mono [Rat.sub_eq_add_neg, Rat.add_neg_cancel]

example (x : Rat) : x / 1 = x := by
  -- smt +mono
  sorry

example (x y : Rat) : x + y - y = x := by
  -- smt_show +mono [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_neg_cancel]
  sorry

example (x : Rat) : x * 0 = 0 := by
  smt +mono [Rat.mul_zero]

example (x : Rat) : x + x = 2 * x := by
  -- smt +mono
  sorry

example (x y : Rat) : x * (y + 1) = x * y + x := by
  smt +mono [Rat.mul_add, Rat.mul_one]
