/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Wojciech Nawrocki
-/

/-!
We define bitvectors. We choose the `Fin` representation over others for its relative efficiency
(`Nat`s reduce in the kernel via GMP), alignment with `UIntXY` types which are also represented
with `Fin`, and the fact that bitwise operations on `Fin` are already defined. Some other possible
representations are `List Bool`, `{ l : List Bool // l.length = w}`, `Fin w → Bool`.

TODO(WN): This is planned to go into mathlib4 once we:
  - prove the various bounds
  - match the interface to what SMT-LIB provides
  - are otherwise happy with the API
-/

def BitVec (w : Nat) := Fin (2^w)

instance : DecidableEq (BitVec w) :=
  inferInstanceAs (DecidableEq (Fin _))

namespace BitVec

protected def zero (w : Nat) : BitVec w :=
  ⟨0, Nat.pos_pow_of_pos _ <| by decide⟩

instance : Inhabited (BitVec w) := ⟨BitVec.zero w⟩

instance : OfNat (BitVec w) (nat_lit 0) :=
  ⟨BitVec.zero w⟩

protected def ofNat (w : Nat) (n : Nat) : BitVec w :=
  Fin.ofNat' n (Nat.pos_pow_of_pos _ <| by decide)

protected def append (x : BitVec w) (y : BitVec v) : BitVec (w+v) :=
  ⟨x.val <<< v ||| y.val, sorry⟩

protected def and (x y : BitVec w) : BitVec w :=
  ⟨x.val &&& y.val, sorry⟩

protected def or (x y : BitVec w) : BitVec w :=
  ⟨x.val ||| y.val, sorry⟩

protected def xor (x y : BitVec w) : BitVec w :=
  ⟨x.val ^^^ y.val, sorry⟩

protected def shiftLeft (x : BitVec w) (n : Nat) : BitVec w :=
  Fin.ofNat' (x.val <<< n) (Nat.pos_pow_of_pos _ (by decide))

protected def shiftRight (x : BitVec w) (n : Nat) : BitVec w :=
  ⟨x.val >>> n, sorry⟩

instance : HAppend (BitVec w) (BitVec v) (BitVec (w+v)) := ⟨BitVec.append⟩
instance : AndOp (BitVec w) := ⟨BitVec.and⟩
instance : OrOp (BitVec w) := ⟨BitVec.or⟩
instance : Xor (BitVec w) := ⟨BitVec.xor⟩
instance : HShiftLeft (BitVec w) Nat (BitVec w) := ⟨BitVec.shiftLeft⟩
instance : HShiftRight (BitVec w) Nat (BitVec w) := ⟨BitVec.shiftRight⟩

def extract (i j : Nat) (x : BitVec w) : BitVec (i - j + 1) :=
  BitVec.ofNat _ (x.val >>> j)

def zeroExtend (v : Nat) (x : BitVec w) (h : w ≤ v) : BitVec v :=
  have hEq : v - w + w = v := Nat.sub_add_cancel h
  hEq ▸ ((0 : BitVec (v - w)) ++ x)

-- `prefix` may be a better name
def shrink (v : Nat) (x : BitVec w) : BitVec v :=
  if hZero : 0 < v then
    have hEq : v - 1 + 0 + 1 = v := by
      rw [Nat.add_zero]
      exact Nat.sub_add_cancel hZero
    hEq ▸ x.extract (v - 1) 0
  else 0

/-- Return the `i`-th least significant bit. -/
def lsbGet (x : BitVec w) (i : Nat) : Bool :=
  x.extract i i != 0

end BitVec
