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

structure BitVec.Packed where
  width : Nat
  data  : Fin (2^width)

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

protected def shiftLeft (x : BitVec w) (n : Nat) : BitVec w :=
  Fin.ofNat' (x.val <<< n) (Nat.pos_pow_of_pos _ (by decide))

protected def shiftRight (x : BitVec w) (n : Nat) : BitVec w :=
  ⟨x.val >>> n, sorry⟩

instance : AndOp (BitVec w) := ⟨BitVec.and⟩
instance : OrOp (BitVec w) := ⟨BitVec.or⟩
instance : Xor (BitVec w) := ⟨BitVec.xor⟩
instance : HShiftLeft (BitVec w) Nat (BitVec w) := ⟨BitVec.shiftLeft⟩
instance : HShiftRight (BitVec w) Nat (BitVec w) := ⟨BitVec.shiftRight⟩

-- TODO re-express as extract == #b0
def lsb_get! (x : BitVec m) (i : Nat) : Bool :=
  (x.val &&& (1 <<< i)) ≠ 0

-- TODO re-express
def lsb_set! (x : BitVec m) (i : Nat) (c : Bool) : BitVec m :=
  if c then
    x ||| ⟨1 <<< i, sorry⟩
  else
    x &&& ⟨((1 <<< m) - 1 - (1 <<< i)), sorry⟩

-- TODO how to zero-extend in SMT-LIB?
def zeroShrinxtend (v : Nat) (x : BitVec w) : BitVec v :=
  if h : w < v then ⟨x.val, Nat.lt_trans x.isLt sorry⟩
  else ⟨x.val % (2^v), Nat.mod_lt _ sorry⟩

end BitVec
