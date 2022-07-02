import Smt
import Smt.Data.BitVec

def polyAdd (a b : BitVec w) : BitVec w := a ^^^ b

/-- Long multiplication in GF(2)[x] translated from Cryptol reference.

```cryptol
pmult : {u, v} (fin u, fin v) => [1 + u] -> [1 + v] -> [1 + u + v]
pmult x y = last zs
  where
    zs = [0] # [ (z << 1) ^ (if yi then 0 # x else 0) | yi <- y | z <- zs ]
``` -/
def polyMul (a : BitVec w) (b : BitVec v) : BitVec (w+v) :=
  let wOut := w + v
  let a := a.zeroShrinxtend wOut
  -- fold over the bits of b starting at MSB
  let ret : BitVec wOut := List.range v |>.foldr (init := 0) fun i acc =>
    let acc' := acc <<< BitVec.ofNat wOut 1
    if b.lsbGet i then polyAdd acc' a else acc'
  ret

-- TODO: it's unfortunate that we have to do this kind of "hand reduction" with custom rules.
-- Could we define everything to reduce as below and then prove all the tail-rec equivalences
-- for efficiency? Then WHNF could go some way towards the goal.

@[simp]
theorem List.range_succ (n : Nat) : List.range (n + 1) = List.range n ++ [n] :=
  sorry

@[simp]
theorem List.range_zero : List.range 0 = [] :=
  sorry

@[simp]
theorem List.foldr_cons (init : β) (f : α → β → β)
    : List.foldr f init (x :: xs) = f x (List.foldr f init xs) :=
  sorry

@[simp]
theorem List.foldr_nil (init : β) (f : α → β → β)
    : List.foldr f init [] = init :=
  sorry

theorem polyMul_comm_8 (x y z w : BitVec 2) : polyAdd (polyMul x y) (polyMul z w) = polyAdd (polyMul w z) (polyMul y x)  := by
  -- What if we could run treat symbols as locally opaque?
  -- The opposite of Carlo's scheme — `opaque foo in t`
  concretize [polyAdd, polyMul, BitVec.zeroShrinxtend, BitVec.lsbGet]

  -- HACK: simp doesn't seem to rewrite
  --   rw [BitVec.zeroShrinxtend.«2».«4».eqVar] at polyMul.«2».«2».eqBody
  -- correctly, so we simp everything out instead
  simp
  concretize [BitVec.zeroShrinxtend]

  smt [BitVec.zeroShrinxtend.«2».«4»]
  sorry
