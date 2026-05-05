import Smt

theorem nat_embedding (f : Nat → Nat → Bool) : f 0 0 = false := by smt

theorem fin_embedding (f : Fin 4 → Fin 4 → Bool) : f 0 0 = false := by smt

theorem fin_bound_free (x : Fin 4) : (x : Nat) < 4 := by smt

theorem fin_bound_output (g : Nat → Fin 4) (a : Nat) : ((g a : Fin 4) : Nat) < 4 := by smt

theorem fin_input_literal (f : Fin 4 → Fin 4 → Bool) : f 0 0 = f 0 0 := by smt
