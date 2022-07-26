/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Wojciech Nawrocki
-/

/-!
We define bitvectors in two variants - indexed and packed. The indexed variant is helpful
for stating strongly-typed interfaces, whereas the packed one is better for stating some
properties without the dependent index getting in the way.

TODO(WN): explain why the particular choice of definition

TODO(WN): This is planned to go into mathlib4 once we:
  - prove the various bounds
  - match the interface to what SMT-LIB provides
  - are otherwise happy with the API
-/

def BitVec (w : Nat) := Fin (2^w)

instance : DecidableEq (BitVec w) :=
  inferInstanceAs (DecidableEq (Fin _))

structure BitVec.Packed where
  width : Nat
  data  : BitVec width

namespace BitVec
namespace Packed

theorem ext {a b : Packed} (hWidth : a.width = b.width)
    (hData : a.data.val = b.data.val) : a = b := by
  let ⟨aw, ad, _⟩ := a
  let ⟨bw, bd, _⟩ := b
  cases hWidth
  cases hData
  rfl

end Packed

protected def zero (w : Nat) : BitVec w :=
  ⟨0, Nat.pos_pow_of_pos _ <| by decide⟩

instance : Inhabited (BitVec w) := ⟨BitVec.zero w⟩

instance : OfNat (BitVec w) (nat_lit 0) :=
  ⟨BitVec.zero w⟩

protected def ofNat (w : Nat) (n : Nat) : BitVec w :=
  Fin.ofNat' n (Nat.pos_pow_of_pos _ <| by decide)

protected def append (x : BitVec w) (y : BitVec v) : BitVec (w+v) :=
  ⟨x.val <<< v ||| y.val, sorry⟩

instance : HAppend (BitVec w) (BitVec v) (BitVec (w+v)) where
  hAppend := BitVec.append

protected def and (x y : BitVec w) : BitVec w :=
  ⟨x.val &&& y.val, sorry⟩

protected def or (x y : BitVec w) : BitVec w :=
  ⟨x.val ||| y.val, sorry⟩

protected def xor (x y : BitVec w) : BitVec w :=
  ⟨x.val ^^^ y.val, sorry⟩

protected def shiftLeft (x y : BitVec w) : BitVec w :=
  Fin.ofNat' (x.val <<< y.val) (Nat.pos_pow_of_pos _ (by decide))

protected def shiftRight (x y : BitVec w) : BitVec w :=
  ⟨x.val >>> y.val, sorry⟩

instance : AndOp (BitVec w) := ⟨BitVec.and⟩
instance : OrOp (BitVec w) := ⟨BitVec.or⟩
instance : Xor (BitVec w) := ⟨BitVec.xor⟩
instance : HShiftLeft (BitVec w) (BitVec w) (BitVec w) := ⟨BitVec.shiftLeft⟩
instance : HShiftRight (BitVec w) (BitVec w) (BitVec w) := ⟨BitVec.shiftRight⟩

def extract (i j : Nat) (x : BitVec w) : BitVec (i - j + 1) :=
  BitVec.ofNat _ (x.val >>> j)

def zeroExtend (v : Nat) (x : BitVec w) (h : w ≤ v) : BitVec v :=
  have hEq : v - w + w = v := Nat.sub_add_cancel h
  hEq ▸ ((0 : BitVec (v - w)) ++ x)

-- `prefix` may be a better name
def shrink (v : Nat) (x : BitVec w) : BitVec v :=
  if hZero : 0 < v then
    have hEq : (v - 1 + 0 + 1) = v := by
      rw [Nat.add_zero]
      exact Nat.sub_add_cancel hZero
    hEq ▸ x.extract (v - 1) 0
  else 0

def lsbGet (x : BitVec w) (i : Nat) : Bool :=
  x.extract i i != 0

-- TODO prove equiv
def lsbGet' (x : BitVec m) (i : Nat) : Bool :=
  (x.val &&& (1 <<< i)) ≠ 0

end BitVec
