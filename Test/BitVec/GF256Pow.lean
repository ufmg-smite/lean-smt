import Lean.Meta.Basic
import Lean.Meta.FunInfo
import Lean.Util.MonadCache

import Smt
import Smt.Data.BitVec
import Smt.Tactic.EqnDef
import Std.Data.HashSet

def polyAdd (a b : BitVec w) : BitVec w := a ^^^ b

def polyMul (a : BitVec w) (b : BitVec v) : BitVec (w+v) :=
  let wOut := w + v
  let_opaque a := a.zeroExtend wOut (Nat.le_add_right _ _)
  -- fold over the bits of b starting at MSB
  let ret : BitVec wOut := List.range v |>.foldr (init := 0) fun i acc =>
    let_opaque acc' := acc <<< BitVec.ofNat wOut 1
    if b.lsbGet i then polyAdd acc' a else acc'
  ret

def polyMod (x : BitVec w) (y : BitVec (v+1)) : BitVec v :=
  if y = 0 then 0
  else
    let reduce (a : BitVec (v+1)) : BitVec (v+1) :=
      if a.lsbGet v then polyAdd a y else a
    let_opaque ret : BitVec v := 0
    let_opaque pow : BitVec (v+1) := reduce (BitVec.ofNat (v+1) 1)
    let (ret, _) := List.range w |>.foldl (init := (ret, pow)) fun (ret, pow) i =>
      let_opaque ret := if x.lsbGet i then polyAdd ret (pow.shrink v) else ret
      let_opaque pow := reduce (pow <<< BitVec.ofNat (v+1) 1)
      (ret, pow)
    ret

namespace GF256

/-- A field element. NB: it does not have to be reduced. -/
abbrev elt := BitVec 8

def elt.ofNat : Nat → elt := BitVec.ofNat 8

def irreducible : BitVec 9 := BitVec.ofNat 9 0b100011011

def add (a b : elt) : elt := polyAdd a b

def mul (a b : elt) : elt := polyMod (polyMul a b) irreducible

def pow (k : Nat) (x : elt) : elt :=
  if hEq : k = 0 then BitVec.ofNat 8 1
  else
    have : k / 2 < k := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hEq) (by decide)
    if k % 2 = 0 then sq (pow (k / 2) x)
    else mul x (sq (pow (k / 2) x))
where
  sq (x : elt) := mul x x

def inverse (x : elt) : elt :=
  pow 254 x

set_option trace.smt.debug true in
set_option maxHeartbeats 1000000 in
-- set_option maxRecDepth 2048 in
set_option trace.Smt.reduce true in
example (x : elt) : pow 256 x = polyMod x irreducible := by
  extract_def pow
  extract_def mul
  extract_def polyMod
  extract_def polyMul
  save

  specialize_def polyMod [16, 8]
  save

  specialize_def polyMod [8, 8]
  save

  specialize_def polyMul [8, 8]
  save

  simp (config := {zeta := false}) only
    [ polyMul.«8».«8».specialization
    , polyMod.«16».«8».specialization
    ]
    at GF256.mul.def
  save

  simp (config := {zeta := false}) only
    [ polyMod.«8».«8».specialization ]
  save

  smt [
    GF256.elt,
    GF256.irreducible,
    GF256.mul,
    GF256.pow.sq,
    GF256.pow,
    polyMod.«16».«8»,
    polyMod.«8».«8»,
    polyMul.«8».«8»
   ]

  sorry

end GF256
