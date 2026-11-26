/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct.Prop.Core

/-!
Definitions and lemmas shared by the bit-vector rewrite rules in
`Smt/Reconstruct/BitVec/Rewrites*.lean`.

SMT-LIB operators are represented as follows (matching `Smt/Translate/BitVec.lean`):

| SMT-LIB                       | Lean                                   |
|-------------------------------|----------------------------------------|
| `(_ bv n w)`                  | `BitVec.ofNat w n` (`n#w`)             |
| `concat`                      | `++`, n-ary: `HBitVecList.concat`      |
| `(_ extract j i) x`           | `x.extractLsb j i`                     |
| `(_ repeat n) x`              | `x.replicate n`                        |
| `(_ zero_extend n) x`         | `x.zeroExtend (w + n)`                 |
| `(_ sign_extend n) x`         | `x.signExtend (w + n)`                 |
| `(_ rotate_left n) x`         | `x.rotateLeft n`                       |
| `bvnot`, `bvneg`              | `~~~x`, `-x`                           |
| `bvand`, `bvor`, `bvxor`      | `&&&`, `|||`, `^^^`, n-ary: `andN` ... |
| `bvadd`, `bvmul`, `bvsub`     | `+`, `*`, `-`, n-ary: `addN`, `mulN`   |
| `bvudiv`, `bvurem`            | `x.smtUDiv y`, `x % y`                 |
| `bvsdiv`, `bvsrem`, `bvsmod`  | `x.smtSDiv y`, `x.srem y`, `x.smod y`  |
| `bvshl`, `bvlshr`, `bvashr`   | `x <<< y`, `x >>> y`, `x.sshiftRight' y` |
| `bvult`, `bvule`              | `x < y`, `x ≤ y`                       |
| `bvugt`, `bvuge`              | `x > y`, `x ≥ y`                       |
| `bvslt`, `bvsle`              | `x.slt y = true`, `x.sle y = true`     |
| `bvsgt`, `bvsge`              | `y.slt x = true`, `y.sle x = true`     |
| `bvuaddo`, `bvsaddo`          | `x.uaddOverflow y = true`, ...         |
| `bvnand`, `bvcomp`, ...       | `x.smtNand y`, `x.smtComp y`, ...      |
| `int.pow2`, `int.log2`        | `2 ^ n`, `n.log2`                      |
| `int.ispow2`                  | `n.isPowerOfTwo`                       |

The n-ary operators are left-associated like the term reconstruction, e.g.,
`andN [x₁, x₂, x₃] = (x₁ &&& x₂) &&& x₃`, and `andN [x] = x`.
-/

@[expose] public section

namespace BitVec

/-! ### SMT-LIB operators without a counterpart in Lean core -/

/-- SMT-LIB `bvnand`. -/
def smtNand (x y : BitVec w) : BitVec w := ~~~(x &&& y)

/-- SMT-LIB `bvnor`. -/
def smtNor (x y : BitVec w) : BitVec w := ~~~(x ||| y)

/-- SMT-LIB `bvxnor`. -/
def smtXnor (x y : BitVec w) : BitVec w := ~~~(x ^^^ y)

/-- SMT-LIB `bvcomp`. -/
def smtComp (x y : BitVec w) : BitVec 1 := if x = y then 1#1 else 0#1

/-- cvc5's `bvredor`: the disjunction of all bits of `x`. -/
def smtRedor (x : BitVec w) : BitVec 1 := if x = 0#w then 0#1 else 1#1

/-- cvc5's `bvredand`: the conjunction of all bits of `x`. -/
def smtRedand (x : BitVec w) : BitVec 1 := if x = allOnes w then 1#1 else 0#1

/-- cvc5's `bvite`: if-then-else with a bit-vector condition of width one. -/
def smtIte (c : BitVec 1) (x y : BitVec w) : BitVec w := if c = 1#1 then x else y

/-! ### n-ary operators -/

/-- n-ary `bvand`. -/
def andN : List (BitVec w) → BitVec w
  | []      => allOnes w
  | x :: xs => xs.foldl (· &&& ·) x

/-- n-ary `bvor`. -/
def orN : List (BitVec w) → BitVec w
  | []      => 0#w
  | x :: xs => xs.foldl (· ||| ·) x

/-- n-ary `bvxor`. -/
def xorN : List (BitVec w) → BitVec w
  | []      => 0#w
  | x :: xs => xs.foldl (· ^^^ ·) x

/-- n-ary `bvadd`. -/
def addN : List (BitVec w) → BitVec w
  | []      => 0#w
  | x :: xs => xs.foldl (· + ·) x

/-- n-ary `bvmul`. -/
def mulN : List (BitVec w) → BitVec w
  | []      => 1#w
  | x :: xs => xs.foldl (· * ·) x

private theorem foldl_assoc {op : α → α → α}
    (assoc : ∀ x y z, op (op x y) z = op x (op y z))
    (x y : α) (xs : List α) : xs.foldl op (op x y) = op x (xs.foldl op y) := by
  induction xs generalizing y with
  | nil => rfl
  | cons z zs ih => simp only [List.foldl_cons, assoc, ih]

@[simp] theorem andN_nil : andN ([] : List (BitVec w)) = allOnes w := rfl
@[simp] theorem andN_singleton {x : BitVec w} : andN [x] = x := rfl
@[simp] theorem andN_cons {x : BitVec w} {xs : List (BitVec w)} :
    andN (x :: xs) = x &&& andN xs := by
  cases xs with
  | nil => simp [andN]
  | cons y ys => exact foldl_assoc and_assoc x y ys
@[simp] theorem andN_append {xs ys : List (BitVec w)} : andN (xs ++ ys) = andN xs &&& andN ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, and_assoc]

@[simp] theorem orN_nil : orN ([] : List (BitVec w)) = 0#w := rfl
@[simp] theorem orN_singleton {x : BitVec w} : orN [x] = x := rfl
@[simp] theorem orN_cons {x : BitVec w} {xs : List (BitVec w)} :
    orN (x :: xs) = x ||| orN xs := by
  cases xs with
  | nil => simp [orN]
  | cons y ys => exact foldl_assoc or_assoc x y ys
@[simp] theorem orN_append {xs ys : List (BitVec w)} : orN (xs ++ ys) = orN xs ||| orN ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, or_assoc]

@[simp] theorem xorN_nil : xorN ([] : List (BitVec w)) = 0#w := rfl
@[simp] theorem xorN_singleton {x : BitVec w} : xorN [x] = x := rfl
@[simp] theorem xorN_cons {x : BitVec w} {xs : List (BitVec w)} :
    xorN (x :: xs) = x ^^^ xorN xs := by
  cases xs with
  | nil => simp [xorN]
  | cons y ys => exact foldl_assoc xor_assoc x y ys
@[simp] theorem xorN_append {xs ys : List (BitVec w)} : xorN (xs ++ ys) = xorN xs ^^^ xorN ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, xor_assoc]

@[simp] theorem addN_nil : addN ([] : List (BitVec w)) = 0#w := rfl
@[simp] theorem addN_singleton {x : BitVec w} : addN [x] = x := rfl
@[simp] theorem addN_cons {x : BitVec w} {xs : List (BitVec w)} :
    addN (x :: xs) = x + addN xs := by
  cases xs with
  | nil => simp [addN]
  | cons y ys => exact foldl_assoc BitVec.add_assoc x y ys
@[simp] theorem addN_append {xs ys : List (BitVec w)} : addN (xs ++ ys) = addN xs + addN ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, BitVec.add_assoc]

@[simp] theorem mulN_nil : mulN ([] : List (BitVec w)) = 1#w := rfl
@[simp] theorem mulN_singleton {x : BitVec w} : mulN [x] = x := rfl
@[simp] theorem mulN_cons {x : BitVec w} {xs : List (BitVec w)} :
    mulN (x :: xs) = x * mulN xs := by
  cases xs with
  | nil => simp [mulN]
  | cons y ys => exact foldl_assoc BitVec.mul_assoc x y ys
@[simp] theorem mulN_append {xs ys : List (BitVec w)} : mulN (xs ++ ys) = mulN xs * mulN ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, BitVec.mul_assoc]

/-! ### Lemmas shared by the rewrite proofs -/

theorem ofNat_two_pow_sub_one {w : Nat} : BitVec.ofNat w (2 ^ w - 1) = allOnes w := by
  apply eq_of_toNat_eq
  rw [toNat_ofNat, toNat_allOnes, Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos)]

/-- A one-bit extract, e.g. `(= (extract n n x) (@bv 1 1))`, compares a single bit of `x`. -/
theorem extractLsb_eq_cast_iff {x : BitVec w} {y : BitVec 1} {h : 1 = n - n + 1} :
    x.extractLsb n n = y.cast h ↔ x.getLsbD n = y.getLsbD 0 := by
  constructor
  · intro he
    have := congrArg (getLsbD · 0) he
    simpa using this
  · intro hb
    apply eq_of_getLsbD_eq
    intro i hi
    obtain rfl : i = 0 := by omega
    simpa using hb

theorem extractLsb_eq_one_iff {x : BitVec w} {h : 1 = n - n + 1} :
    x.extractLsb n n = (1#1).cast h ↔ x.getLsbD n = true := by
  rw [extractLsb_eq_cast_iff, getLsbD_one]; rfl

theorem extractLsb_eq_zero_iff {x : BitVec w} {h : 1 = n - n + 1} :
    x.extractLsb n n = (0#1).cast h ↔ x.getLsbD n = false := by
  rw [extractLsb_eq_cast_iff, getLsbD_zero]

theorem extractLsb_msb_eq_cast_iff {x : BitVec w} {y : BitVec 1} (hn : n = w - 1)
    {h : 1 = n - n + 1} : x.extractLsb n n = y.cast h ↔ x.msb = y.getLsbD 0 := by
  rw [extractLsb_eq_cast_iff, msb_eq_getLsbD_last, hn]

theorem extractLsb_msb_eq_one_iff {x : BitVec w} (hn : n = w - 1) {h : 1 = n - n + 1} :
    x.extractLsb n n = (1#1).cast h ↔ x.msb = true := by
  rw [extractLsb_eq_one_iff, msb_eq_getLsbD_last, hn]

theorem extractLsb_msb_eq_zero_iff {x : BitVec w} (hn : n = w - 1) {h : 1 = n - n + 1} :
    x.extractLsb n n = (0#1).cast h ↔ x.msb = false := by
  rw [extractLsb_eq_zero_iff, msb_eq_getLsbD_last, hn]

end BitVec

/-! ### Heterogeneous lists of bit-vectors (`:list` arguments of `concat`) -/

/-- A list of bit-vectors of possibly different widths. -/
inductive HBitVecList where
  /-- The empty list. -/
  | nil : HBitVecList
  /-- Prepend a bit-vector to the list. -/
  | cons {w : Nat} (x : BitVec w) (xs : HBitVecList) : HBitVecList

namespace HBitVecList

@[inherit_doc] infixr:67 " ::ₕ " => HBitVecList.cons

/-- Append two heterogeneous lists of bit-vectors. -/
protected def append : HBitVecList → HBitVecList → HBitVecList
  | nil,     ys => ys
  | x ::ₕ xs, ys => x ::ₕ xs.append ys

instance : Append HBitVecList := ⟨HBitVecList.append⟩

@[simp] theorem nil_append {xs : HBitVecList} : nil ++ xs = xs := rfl
@[simp] theorem cons_append {x : BitVec w} {xs ys : HBitVecList} :
    (x ::ₕ xs) ++ ys = x ::ₕ (xs ++ ys) := rfl
@[simp] theorem append_nil {xs : HBitVecList} : xs ++ nil = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [cons_append, ih]
theorem append_assoc {xs ys zs : HBitVecList} : xs ++ ys ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [cons_append, ih]

/-- Width of the left-associated concatenation of `xs` onto a bit-vector of width `v`. -/
def widthAux (v : Nat) : HBitVecList → Nat
  | nil               => v
  | cons (w := w) _ xs => widthAux (v + w) xs

/-- Width of the concatenation of `xs`. -/
def width : HBitVecList → Nat
  | nil               => 0
  | cons (w := w) _ xs => widthAux w xs

/-- Left-associated concatenation of `xs` onto `acc`. -/
def concatAux (acc : BitVec v) : (xs : HBitVecList) → BitVec (widthAux v xs)
  | nil     => acc
  | x ::ₕ xs => concatAux (acc ++ x) xs

/-- n-ary SMT-LIB `concat`, left-associated like the term reconstruction:
`concat (x₁ ::ₕ x₂ ::ₕ x₃ ::ₕ nil) = (x₁ ++ x₂) ++ x₃` and
`concat (x ::ₕ nil) = x`. -/
def concat : (xs : HBitVecList) → BitVec xs.width
  | nil     => .nil
  | x ::ₕ xs => concatAux x xs

theorem widthAux_eq {v : Nat} {xs : HBitVecList} : widthAux v xs = v + xs.width := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih => simp only [widthAux, width, ih]; omega

@[simp] theorem width_nil : nil.width = 0 := rfl
@[simp] theorem width_cons {x : BitVec w} {xs : HBitVecList} : (x ::ₕ xs).width = w + xs.width :=
  widthAux_eq
@[simp] theorem width_append {xs ys : HBitVecList} : (xs ++ ys).width = xs.width + ys.width := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [cons_append, width_cons, ih]; omega

theorem toNat_concatAux {acc : BitVec v} {xs : HBitVecList} :
    (concatAux acc xs).toNat = acc.toNat <<< xs.width ||| xs.concat.toNat := by
  induction xs generalizing v with
  | nil => show acc.toNat = acc.toNat <<< 0 ||| (0#0).toNat; simp
  | cons x xs ih =>
    show (concatAux (acc ++ x) xs).toNat =
      acc.toNat <<< (x ::ₕ xs).width ||| (concatAux x xs).toNat
    rw [ih, ih, width_cons, BitVec.toNat_append, Nat.shiftLeft_or_distrib, Nat.or_assoc,
      Nat.shiftLeft_add]

theorem concatAux_eq {acc : BitVec v} {xs : HBitVecList} :
    concatAux acc xs = (acc ++ xs.concat).cast widthAux_eq.symm := by
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_concatAux, BitVec.toNat_cast, BitVec.toNat_append]

@[simp] theorem concat_nil : nil.concat = .nil := rfl
@[simp] theorem concat_singleton {x : BitVec w} : (x ::ₕ nil).concat = x := rfl
@[simp] theorem getLsbD_concat_singleton {x : BitVec w} {i : Nat} :
    (x ::ₕ nil).concat.getLsbD i = x.getLsbD i := rfl
theorem concat_cons {x : BitVec w} {xs : HBitVecList} :
    (x ::ₕ xs).concat = (x ++ xs.concat).cast width_cons.symm :=
  concatAux_eq

@[simp] theorem toNat_concat_cons {x : BitVec w} {xs : HBitVecList} :
    (x ::ₕ xs).concat.toNat = x.toNat <<< xs.width ||| xs.concat.toNat := by
  rw [concat_cons, BitVec.toNat_cast, BitVec.toNat_append]

@[simp] theorem toNat_concat_append {xs ys : HBitVecList} :
    (xs ++ ys).concat.toNat = xs.concat.toNat <<< ys.width ||| ys.concat.toNat := by
  induction xs with
  | nil => show ys.concat.toNat = (0#0).toNat <<< ys.width ||| ys.concat.toNat; simp
  | cons x xs ih =>
    rw [cons_append, toNat_concat_cons, ih, toNat_concat_cons, width_append,
      Nat.shiftLeft_or_distrib, Nat.or_assoc, Nat.shiftLeft_add]

theorem concat_append {xs ys : HBitVecList} :
    (xs ++ ys).concat = (xs.concat ++ ys.concat).cast width_append.symm := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_concat_append, BitVec.toNat_cast, BitVec.toNat_append]

@[simp] theorem getLsbD_concat_cons {x : BitVec w} {xs : HBitVecList} {i : Nat} :
    (x ::ₕ xs).concat.getLsbD i =
      if i < xs.width then xs.concat.getLsbD i else x.getLsbD (i - xs.width) := by
  rw [concat_cons, BitVec.getLsbD_cast, BitVec.getLsbD_append]

@[simp] theorem getLsbD_concat_append {xs ys : HBitVecList} {i : Nat} :
    (xs ++ ys).concat.getLsbD i =
      if i < ys.width then ys.concat.getLsbD i else xs.concat.getLsbD (i - ys.width) := by
  rw [concat_append, BitVec.getLsbD_cast, BitVec.getLsbD_append]

end HBitVecList
