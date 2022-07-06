import Smt
import Smt.Data.BitVec

def polyAdd (a b : BitVec w) : BitVec w := a ^^^ b

def polyMul (a : BitVec w) (b : BitVec v) : BitVec (w+v) :=
  let wOut := w + v
  let a := a.zeroShrinxtend wOut
  -- fold over the bits of b starting at MSB
  let ret : BitVec wOut := List.range v |>.foldr (init := 0) fun i acc =>
    let acc' := acc <<< BitVec.ofNat wOut 1
    if b.lsbGet i then polyAdd acc' a else acc'
  ret

def polyMod (x : BitVec w) (y : BitVec (v+1)) : BitVec v :=
  if y = 0 then 0
  else
    let reduce (a : BitVec (v+1)) : BitVec (v+1) := if a.lsbGet (v-1) then polyAdd a y else a
    let ret : BitVec v := 0
    let pow : BitVec (v+1) := reduce ⟨1, by
      show 1 * 2 ≤ 2^v * 2
      exact Nat.mul_le_mul_right 2 <| Nat.succ_le_of_lt <| Nat.pos_pow_of_pos _ <| by decide⟩
    let (ret, _) := List.range w |>.foldl (init := (ret, pow)) fun (ret, pow) i =>
      let pow := reduce (pow <<< BitVec.ofNat (v+1) 1)
      if x.lsbGet i then (polyAdd ret (pow.zeroShrinxtend v), pow)
      else (ret, pow)
    ret

namespace GF256

/-- A field element. -/
abbrev elt := BitVec 8

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
example (x : elt) : pow 256 x = x := by
  concretize [pow]
  let z := pow 256 x
  have : pow 256 x = z := rfl
  rw [this]
  smt [pow, elt]

end GF256
