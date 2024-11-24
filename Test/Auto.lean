import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Function

import Smt
import Smt.Auto

set_option auto.native true

example {α : Type} (x : α) : List.head? [x] = .some x := by
  have h₂ : ∀ (x : α) (ys : _), List.head? (x :: ys) = .some x := fun _ _ => rfl
  auto

example {α : Type} (x y : α) : [x] ++ [y] = [x, y] := by
  -- Invoke definition unfolding
  have h : ∀ (x y : List α), x ++ y = x.append y := fun _ _ => rfl
  auto [h] d[List.append]

variable {G : Type} [Group G]

theorem inverse' : ∀ (a : G), a * a⁻¹ = 1 := by
  auto [mul_assoc, one_mul, inv_mul_cancel]

theorem identity' : ∀ (a : G), a * 1 = a := by
  auto [mul_assoc, one_mul, inv_mul_cancel, inverse']

theorem unique_identity (e : G) : (∀ z, e * z = z) → e = 1 := by
  auto [mul_assoc, one_mul, inv_mul_cancel]

-- TODO: pre-process Nat away
-- example {α : Type} (x y : α) : List.get? [x, y] 1 = .some y := by
  -- auto d[List.get?]

set_option auto.mono.mode "fol"

variable {α β : Type} [Nonempty α] [Nonempty β] {f : α → β} {s : Set α} {v u : Set β}

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  auto [Set.subset_def, Set.mem_image, Set.mem_preimage]

example (h : Function.Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  auto [Set.subset_def, Set.mem_preimage, Function.Injective.mem_set_image, h]

example : f '' (f ⁻¹' u) ⊆ u := by
  auto [Set.subset_def, Set.mem_image, Set.mem_preimage]

example (h : Function.Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  unfold Function.Surjective at h
  auto [Set.subset_def, Set.mem_image, Set.mem_preimage, h]
