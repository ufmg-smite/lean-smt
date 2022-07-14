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
    let acc' := acc <<< 1
    if b.lsb_get! i then polyAdd acc' a else acc'
  ret

theorem polyMul_comm_8 (x y z w : BitVec 2) : polyAdd (polyMul x y) (polyMul z w) = polyAdd (polyMul w z) (polyMul y x)  := by
  concretize [polyAdd, polyMul]
  smt [polyAdd.«4», polyMul.«2».«2»]
  sorry
