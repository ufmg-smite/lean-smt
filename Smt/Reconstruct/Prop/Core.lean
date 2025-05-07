/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

/- abbrev Implies (p q : Prop) := p → q -/

inductive XOr (p q : Prop) : Prop where
  | inl : p → ¬q → XOr p q
  | inr : ¬p → q → XOr p q

theorem XOr.elim {p q r : Prop} (h : XOr p q) (h₁ : p → ¬q → r) (h₂ : ¬p → q → r) : r := match h with
  | inl hp hnq => h₁ hp hnq
  | inr hnp hq => h₂ hnp hq

theorem XOr.symm (h : XOr p q) : XOr q p := h.elim (flip inr) (flip inl)

namespace XOr

@[macro_inline] instance [dp : Decidable p] [dq : Decidable q] : Decidable (XOr p q) :=
  match dp with
  | isTrue   hp =>
    match dq with
    | isTrue   hq => isFalse (·.elim (fun _ hnq => hnq hq) (fun hnp _ => hnp hp))
    | isFalse hnq => isTrue (.inl hp hnq)
  | isFalse hnp =>
    match dq with
    | isTrue   hq => isTrue (.inr hnp hq)
    | isFalse hnq => isFalse (·.elim (fun hp _ => hnp hp) (fun _ hq => hnq hq))

end XOr

def andN : List Prop → Prop
  | []      => True
  | p :: [] => p
  | p :: ps => p ∧ andN ps

@[simp] theorem andN_append : andN (ps ++ qs) = (andN ps ∧ andN qs) := by
  match ps, qs with
  | [], _
  | [p], []
  | [p], q :: qs       => simp [andN]
  | p₁ :: p₂ :: ps, qs =>
    rw [List.cons_append, andN, andN, andN_append, and_assoc]
    all_goals (intro h; nomatch h)

@[simp] theorem andN_cons_append : andN (p :: ps) = (p ∧ andN ps) := by
  cases ps <;> simp only [andN, and_true]

def orN : List Prop → Prop
  | []      => False
  | p :: [] => p
  | p :: qs => p ∨ orN qs

@[simp] theorem orN_append : orN (ps ++ qs) = (orN ps ∨ orN qs) := by
  match ps, qs with
  | [], _
  | [p], []
  | [p], q :: qs       => simp [orN]
  | p₁ :: p₂ :: ps, qs =>
    rw [List.cons_append, orN, orN, orN_append, or_assoc]
    all_goals (intro h; nomatch h)

@[simp] theorem orN_cons_append : orN (p :: ps) = (p ∨ orN ps) := by
  cases ps <;> simp only [orN, or_false]

def impliesN (ps : List Prop) (q : Prop) : Prop := match ps with
  | [] => q
  | p :: ps => p → impliesN ps q

def notN : List Prop → List Prop := List.map Not

namespace Smt.Reconstruct.Prop

theorem and_assoc_eq : ((p ∧ q) ∧ r) = (p ∧ (q ∧ r)) := by
  simp [and_assoc]

theorem and_comm_eq : (p ∧ q) = (q ∧ p) := by
  simp [and_comm]

theorem or_assoc_eq : ((a ∨ b) ∨ c) = (a ∨ (b ∨ c)) := by
  simp [or_assoc]

theorem or_comm_eq : (p ∨ q) = (q ∨ p) := by
  simp [or_comm]

instance : Std.Associative And := ⟨@and_assoc_eq⟩

instance : Std.Commutative And := ⟨@and_comm_eq⟩

instance : Std.IdempotentOp And := ⟨and_self⟩

instance : Std.LawfulIdentity And True where
  left_id := true_and
  right_id := and_true

instance : Std.Associative Or := ⟨@or_assoc_eq⟩

instance : Std.Commutative Or := ⟨@or_comm_eq⟩

instance : Std.IdempotentOp Or := ⟨or_self⟩

instance : Std.LawfulIdentity Or False where
  left_id := false_or
  right_id := or_false

end Smt.Reconstruct.Prop
