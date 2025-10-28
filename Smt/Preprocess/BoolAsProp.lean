import Smt.Reconstruct.Prop.Core

theorem Bool.not_eq_true2 (x : Bool) : (!x : Bool) = ¬(x : Prop) := by
  rw [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_true]

theorem Bool.iff_eq_true (x y : Bool) : (x ↔ y : Bool) = ((x : Prop) ↔ (y : Prop)) := by
  simp only [Bool.coe_iff_coe, decide_eq_true_eq]

theorem Bool.xor_eq_true (x y : Bool) : (x ^^ y : Bool) = (XOr (x : Prop) (y : Prop)) := by
  cases x <;> cases y <;> decide

theorem Bool.eq_eq_true (x y : Bool) : (x = y : Bool) = ((x : Prop) = (y : Prop)) := by
  simp only [decide_eq_true_eq, _root_.eq_iff_iff, coe_iff_coe]

theorem Bool.eq_self (x : Bool): (x = x) = (True : Prop) := by
  simp only

theorem Prop.eq_true (x : Prop) : (x = True : Prop) = (x : Prop) := by
  simp only [eq_iff_iff, iff_true]

theorem Prop.eq_false (x : Prop) : (x = False : Prop) = (¬x : Prop) := by
  simp only [eq_iff_iff, iff_false]
