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

-- TODO Translating do-notation is a nightmare :(
-- Would partial reduction with opaqueness unfold things correctly?

-- def polyMod (x : BitVec w) (y : BitVec (v+1)) : BitVec v :=
--   if y = 0 then 0
--   else Id.run do
--     let mut ret : BitVec v := 0
--     let reduce (a : BitVec (v+1)) : BitVec (v+1) := if a.lsbGet 7 /- HACK -/ then polyAdd a y else a
--     let mut pow : BitVec (v+1) := reduce ⟨1, by
--       show 1 * 2 ≤ 2^v * 2
--       exact Nat.mul_le_mul_right 2 <| Nat.succ_le_of_lt <| Nat.pos_pow_of_pos _ <| by decide⟩
--     for i in List.range w do
--       if x.lsbGet i then ret := polyAdd ret (pow.zeroShrinxtend v)
--       pow := reduce (pow <<< BitVec.ofNat (v+1) 1)
--     return ret

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

@[simp]
theorem List.range_succ (n : Nat) : List.range (n + 1) = List.range n ++ [n] :=
  sorry

@[simp]
theorem List.range_zero : List.range 0 = [] :=
  sorry

@[simp]
theorem List.foldl_cons (init : β) (f : β → α → β)
    : List.foldl f init (x :: xs) = f (List.foldl f init xs) x :=
  sorry

@[simp]
theorem List.foldl_nil (init : β) (f : β → α → β)
    : List.foldl f init [] = init :=
  sorry

set_option trace.smt.debug true in
theorem mul_comm (x y : elt) : mul x y = mul y x := by
  unfold mul
  with_unfolding_all concretize [polyMod, polyMul, polyAdd]
  smt [irreducible, elt]

  sorry

end GF256
