/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public section

namespace Smt.Reconstruct.BitVec.Rewrite

-- https://github.com/cvc5/cvc5/blob/main/src/theory/bv/rewrites-simplification

variable {w : Nat} {x : BitVec w}

theorem xor_duplicate : x ^^^ x = BitVec.ofNat w 0 := by
  simp
theorem ult_zero_1 : (BitVec.ofNat w 0 < x) = ¬(x = BitVec.ofNat w 0) := by
  apply propext
  simp only [BitVec.lt_def, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod]
  omega
theorem ult_zero_2 : (x < BitVec.ofNat w 0) = False := by
  simp
theorem udiv_one : x.smtUDiv (BitVec.ofNat w 1) = x := by
  rcases w with _ | w
  · exact Subsingleton.elim _ _
  · simp [BitVec.smtUDiv]

end Smt.Reconstruct.BitVec.Rewrite
