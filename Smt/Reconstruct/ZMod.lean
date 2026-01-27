/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/
import Smt.Reconstruct
import Mathlib.Data.ZMod.Basic

@[smt_sort_reconstruct] def reconstructBitVecSort : SortReconstructor := fun s => do match s.getKind with
  | .BITVECTOR_SORT =>
    let w : Nat := s.getBitVectorSize!.toNat
    return q(BitVec $w)
  | _             => return none

  @[smt_term_reconstruct] def reconstructBitVec : TermReconstructor := fun t => do match t.getKind with
  | .CONST_BITVECTOR =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let v : Nat := (t.getBitVectorValue! 10).toNat!
    return q(BitVec.ofNat $w $v)
  | .BITVECTOR_CONCAT =>
    let n : Nat := t.getNumChildren
    let w₁ : Nat := t[0]!.getSort.getBitVectorSize!.toNat
    let a : Q(BitVec $w₁) ← reconstructTerm t[0]!
    let f := fun ⟨w₁, a⟩ i => do
      let w₂ : Nat := t[i]!.getSort.getBitVectorSize!.toNat
      let x : Q(BitVec $w₂) ← reconstructTerm t[i]!
      return ⟨q($w₁ + $w₂), q($a ++ $x)⟩
    let ⟨_, a⟩ ← [1:n].foldlM f (⟨q($w₁), a⟩ : Σ w : Q(Nat), Q(BitVec $w))
    return a
  | .BITVECTOR_AND =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    leftAssocOp q(@AndOp.and (BitVec $w) _) t
  | .BITVECTOR_OR =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    leftAssocOp q(@OrOp.or (BitVec $w) _) t
  | .BITVECTOR_XOR =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    leftAssocOp q(@XorOp.xor (BitVec $w) _) t
  | .BITVECTOR_NOT =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(~~~$x)
  | .BITVECTOR_MULT =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    leftAssocOp q(@HMul.hMul (BitVec $w) (BitVec $w) (BitVec $w) _) t
  | .BITVECTOR_ADD =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    leftAssocOp q(@HAdd.hAdd (BitVec $w) (BitVec $w) (BitVec $w) _) t
  | .BITVECTOR_SUB =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    leftAssocOp q(@HSub.hSub (BitVec $w) (BitVec $w) (BitVec $w) _) t
  | .BITVECTOR_NEG =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(-$x)
  | .BITVECTOR_UDIV =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.smtUDiv $x $y)
  | .BITVECTOR_UREM =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x % $y)
  | .BITVECTOR_SDIV =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.smtSDiv $x $y)
  | .BITVECTOR_SREM =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.srem $x $y)
  | .BITVECTOR_SMOD =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.smod $x $y)
  | .BITVECTOR_SHL =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let i : Nat := t.getOp![0]!.getIntegerValue!.toNat
    return q($x <<< $i)
  | .BITVECTOR_LSHR =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let i : Nat := t.getOp![0]!.getIntegerValue!.toNat
    return q($x >>> $i)
  | .BITVECTOR_ASHR =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let i : Nat := t.getOp![0]!.getIntegerValue!.toNat
    return q(BitVec.sshiftRight $x $i)
  | .BITVECTOR_ULT =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x < $y)
  | .BITVECTOR_ULE =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x ≤ $y)
  | .BITVECTOR_UGT =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x > $y)
  | .BITVECTOR_UGE =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x ≥ $y)
  | .BITVECTOR_SLT =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.slt $x $y)
  | .BITVECTOR_SLE =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.sle $x $y)
  | .BITVECTOR_EXTRACT =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let i : Nat := t.getOp![0]!.getIntegerValue!.toNat
    let j : Nat := t.getOp![1]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».extractLsb $i $j)
  | .BITVECTOR_REPEAT =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let n : Nat := t.getOp![0]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».replicate $n)
  | .BITVECTOR_ZERO_EXTEND =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let n : Nat := t.getOp![0]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».zeroExtend $n)
  | .BITVECTOR_SIGN_EXTEND =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let n : Nat := t.getOp![0]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».signExtend $n)
  | .BITVECTOR_ROTATE_LEFT =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let n : Nat := t.getOp![0]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».rotateLeft $n)
  | .BITVECTOR_ROTATE_RIGHT =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let n : Nat := t.getOp![0]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».rotateRight $n)
  | .INT_TO_BITVECTOR =>
    let w : Nat := t.getSort.getBitVectorSize!.toNat
    let x : Q(Int) ← reconstructTerm t[0]!
    return q(BitVec.ofNat $w «$x».toNat)
  | .BITVECTOR_TO_NAT =>
    let w : Nat := t[0]!.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».toNat)
  | .BITVECTOR_FROM_BOOLS =>
    let w : Nat := t.getNumChildren
    let bs : Q(BitVec 0) := q(.nil)
    let f (bs : Expr) (i : Nat) : ReconstructM Expr := do
      let p : Q(Prop) ← reconstructTerm t[i]!
      let bs : Q(BitVec $i) := bs
      let hp : Q(Decidable $p) ← synthDecidableInst t[i]!
      return q(@BitVec.cons $i (@decide $p $hp) $bs)
    let bs : Q(BitVec $w) ← (List.range w).foldlM f bs
    return q($bs)
  | .BITVECTOR_BIT =>
    let w : Nat := t[0]!.getSort.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let i : Nat := t.getOp![0]!.getIntegerValue!.toNat
    return q(«$x».getLsbD $i = true)
  | _ => return none
where
  leftAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op curr (← reconstructTerm t[i]!)
    return curr
