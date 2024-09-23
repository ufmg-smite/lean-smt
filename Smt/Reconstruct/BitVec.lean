/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct.Bool.Tactic
import Smt.Reconstruct.BitVec.Bitblast
import Smt.Reconstruct.Prop.Core
import Smt.Reconstruct

def Std.Range.foldlM [Monad m] (f : α → Nat → m α) (r : Range) (init : α) : m α := do
  let mut a := init
  for i in r do
    a ← f a i
  return a

namespace Smt.Reconstruct.BitVec

open Lean Qq

@[smt_sort_reconstruct] def reconstructBitVecSort : SortReconstructor := fun s => do match s.getKind with
  | .BITVECTOR_SORT =>
    let w : Nat := s.getBitVectorSize.val
    return q(BitVec $w)
  | _             => return none

partial def synthDecidableInst (t : cvc5.Term) : ReconstructM Expr := do match t.getKind with
    | .CONST_BOOLEAN => return if t.getBooleanValue then q(instDecidableTrue) else q(instDecidableFalse)
    | .NOT =>
      let p : Q(Prop) ← reconstructTerm t[0]!
      let hp : Q(Decidable $p) ← synthDecidableInst t[0]!
      return q(@instDecidableNot $p $hp)
    | .AND => rightAssocOpDecidableInst q(And) q(@instDecidableAnd) t
    | .OR => rightAssocOpDecidableInst q(Or) q(@instDecidableOr) t
    | .XOR => rightAssocOpDecidableInst q(XOr) q(@XOr.instDecidable) t
    | .EQUAL =>
      if t[0]!.getSort.getKind == .BOOLEAN_SORT then
        let p : Q(Prop) ← reconstructTerm t[0]!
        let q : Q(Prop) ← reconstructTerm t[1]!
        let hp : Q(Decidable $p) ← synthDecidableInst t[0]!
        let hq : Q(Decidable $q) ← synthDecidableInst t[1]!
        return q(@instDecidableEqOfIff $p $q (@instDecidableIff $p $q $hp $hq))
      if t[0]!.getSort.getKind == .BITVECTOR_SORT then
        let w : Nat := t[0]!.getSort.getBitVectorSize.val
        return q(@instDecidableEqBitVec $w)
      let p : Q(Prop) ← reconstructTerm t
      Meta.synthInstance q(Decidable $p)
    | .BITVECTOR_BIT =>
      let w : Nat := t[0]!.getSort.getBitVectorSize.val
      let x : Q(BitVec $w) ← reconstructTerm t[0]!
      let i : Nat := t.getOp[0]!.getIntegerValue.toNat
      return q(instDecidableEqBool («$x».getLsb $i) true)
    | _ =>
      let p : Q(Prop) ← reconstructTerm t
      Meta.synthInstance q(Decidable $p)
where
   rightAssocOpDecidableInst (op : Expr) (inst : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[t.getNumChildren - 1]!
    let mut currInst ← synthDecidableInst t[t.getNumChildren - 1]!
    for i in [1:t.getNumChildren] do
      let ct := t[t.getNumChildren - i - 1]!
      currInst := mkApp4 inst (← reconstructTerm ct) curr (← synthDecidableInst ct) currInst
      curr := mkApp2 op (← reconstructTerm ct) curr
    return currInst

@[smt_term_reconstruct] def reconstructBitVec : TermReconstructor := fun t => do match t.getKind with
  | .CONST_BITVECTOR =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let v : Nat := (t.getBitVectorValue 10).toNat!
    return q(BitVec.ofNat $w $v)
  | .BITVECTOR_CONCAT =>
    let n : Nat := t.getNumChildren
    let w₁ : Nat := t[0]!.getSort.getBitVectorSize.val
    let a : Q(BitVec $w₁) ← reconstructTerm t[0]!
    let f := fun ⟨w₁, a⟩ i => do
      let w₂ : Nat := t[i]!.getSort.getBitVectorSize.val
      let x : Q(BitVec $w₂) ← reconstructTerm t[i]!
      return ⟨q($w₁ + $w₂), q($a ++ $x)⟩
    let ⟨_, a⟩ ← [1:n].foldlM f (⟨q($w₁), a⟩ : Σ w : Q(Nat), Q(BitVec $w))
    return a
  | .BITVECTOR_AND =>
    let w : Nat := t.getSort.getBitVectorSize.val
    leftAssocOp q(@AndOp.and (BitVec $w) _) t
  | .BITVECTOR_OR =>
    let w : Nat := t.getSort.getBitVectorSize.val
    leftAssocOp q(@OrOp.or (BitVec $w) _) t
  | .BITVECTOR_XOR =>
    let w : Nat := t.getSort.getBitVectorSize.val
    leftAssocOp q(@Xor.xor (BitVec $w) _) t
  | .BITVECTOR_NOT =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(~~~$x)
  | .BITVECTOR_MULT =>
    let w : Nat := t.getSort.getBitVectorSize.val
    leftAssocOp q(@HMul.hMul (BitVec $w) (BitVec $w) (BitVec $w) _) t
  | .BITVECTOR_ADD =>
    let w : Nat := t.getSort.getBitVectorSize.val
    leftAssocOp q(@HAdd.hAdd (BitVec $w) (BitVec $w) (BitVec $w) _) t
  | .BITVECTOR_SUB =>
    let w : Nat := t.getSort.getBitVectorSize.val
    leftAssocOp q(@HSub.hSub (BitVec $w) (BitVec $w) (BitVec $w) _) t
  | .BITVECTOR_NEG =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(-$x)
  | .BITVECTOR_UDIV =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.smtUDiv $x $y)
  | .BITVECTOR_UREM =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x % $y)
  | .BITVECTOR_SDIV =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.smtSDiv $x $y)
  | .BITVECTOR_SREM =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.srem $x $y)
  | .BITVECTOR_SMOD =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.smod $x $y)
  | .BITVECTOR_SHL =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let i : Nat := t.getOp[0]!.getIntegerValue.toNat
    return q($x <<< $i)
  | .BITVECTOR_LSHR =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let i : Nat := t.getOp[0]!.getIntegerValue.toNat
    return q($x >>> $i)
  | .BITVECTOR_ASHR =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let i : Nat := t.getOp[0]!.getIntegerValue.toNat
    return q(BitVec.sshiftRight $x $i)
  | .BITVECTOR_ULT =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x < $y)
  | .BITVECTOR_ULE =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x ≤ $y)
  | .BITVECTOR_UGT =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x > $y)
  | .BITVECTOR_UGE =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x ≥ $y)
  | .BITVECTOR_SLT =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.slt $x $y)
  | .BITVECTOR_SLE =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.sle $x $y)
  | .BITVECTOR_EXTRACT =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let i : Nat := t.getOp[0]!.getIntegerValue.toNat
    let j : Nat := t.getOp[1]!.getIntegerValue.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».extractLsb $i $j)
  | .BITVECTOR_REPEAT =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let n : Nat := t.getOp[0]!.getIntegerValue.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».replicate $n)
  | .BITVECTOR_ZERO_EXTEND =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let n : Nat := t.getOp[0]!.getIntegerValue.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».zeroExtend $n)
  | .BITVECTOR_SIGN_EXTEND =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let n : Nat := t.getOp[0]!.getIntegerValue.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».signExtend $n)
  | .BITVECTOR_ROTATE_LEFT =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let n : Nat := t.getOp[0]!.getIntegerValue.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».rotateLeft $n)
  | .BITVECTOR_ROTATE_RIGHT =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let n : Nat := t.getOp[0]!.getIntegerValue.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».rotateRight $n)
  | .INT_TO_BITVECTOR =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(Int) ← reconstructTerm t[0]!
    return q(BitVec.ofNat $w «$x».toNat)
  | .BITVECTOR_TO_NAT =>
    let w : Nat := t[0]!.getSort.getBitVectorSize.val
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
    let w : Nat := t[0]!.getSort.getBitVectorSize.val
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let i : Nat := t.getOp[0]!.getIntegerValue.toNat
    return q(«$x».getLsb $i = true)
  | _ => return none
where
  leftAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op curr (← reconstructTerm t[i]!)
    return curr

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule with
  | _ => return none

@[smt_proof_reconstruct] def reconstructBitVecProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE => reconstructRewrite pf
  | .BV_BITBLAST_STEP =>
    let t := pf.getArguments[0]![0]!
    match t.getKind with
    | .CONST_BITVECTOR =>
      let w : Nat := t.getSort.getBitVectorSize.toNat
      let t : Q(BitVec $w) ← reconstructTerm pf.getResult[0]!
      let t' : Q(BitVec $w) ← reconstructTerm pf.getResult[1]!
      addThm q($t = $t') q(Eq.refl $t)
    | .CONSTANT =>
      let w : Nat := t.getSort.getBitVectorSize.toNat
      let x : Q(BitVec $w) ← reconstructTerm pf.getResult[0]!
      let x' : Q(BitVec $w) ← reconstructTerm pf.getResult[1]!
      let h : Q(«$x».bb = $x') ← Meta.mkFreshExprMVar q(«$x».bb = $x')
      let mv ← Bool.boolify h.mvarId!
      let ds := [``BitVec.bb, ``BitVec.iunfoldr, ``Fin.hIterate, ``Fin.hIterateFrom]
      let ps := [``Nat.reduceAdd, ``Nat.reduceLT, ``reduceDIte]
      let simpTheorems ← ds.foldrM (fun n a => a.addDeclToUnfold n) {}
      let simpProcs ← ps.foldrM (fun n a => a.add n false) {}
      let (some mv, _) ← Meta.simpTarget mv { simpTheorems := #[simpTheorems] } simpProcs | throwError "simp failed"
      mv.refl
      addThm q($x = $x') q(Eq.trans (BitVec.self_eq_bb $x) $h)
    | .EQUAL =>
      let w : Nat := t[0]!.getSort.getBitVectorSize.toNat
      let x : Q(BitVec $w) ← reconstructTerm pf.getResult[0]![0]!
      let y : Q(BitVec $w) ← reconstructTerm pf.getResult[0]![1]!
      let p : Q(Prop) ← reconstructTerm pf.getResult[1]!
      let hp : Q(Decidable $p) ← synthDecidableInst pf.getResult[1]!
      let h : Q(decide (BitVec.beq $x $y) = decide $p) ← Meta.mkFreshExprMVar q(decide (BitVec.beq $x $y) = @decide $p $hp)
      let mv ← Bool.boolify h.mvarId!
      let ds := [``BitVec.beq, ``BitVec.beq.go]
      let ts := [``BitVec.getLsb_cons, ``Nat.succ.injEq]
      let ps := [``Nat.reduceAdd, ``Nat.reduceSub, ``Nat.reduceEqDiff, ``reduceIte]
      let simpTheorems ← ds.foldrM (fun n a => a.addDeclToUnfold n) {}
      let simpTheorems ← ts.foldrM (fun n a => a.addConst n) simpTheorems
      let simpProcs ← ps.foldrM (fun n a => a.add n false) {}
      let (some mv, _) ← Meta.simpTarget mv { simpTheorems := #[simpTheorems] } simpProcs | throwError "simp failed"
      mv.refl
      addThm q(($x = $y) = $p) q(Eq.trans (BitVec.eq_eq_beq $x $y) (Bool.eq_of_decide_eq $h))
    | .BITVECTOR_ADD =>
      let w : Nat := t[0]!.getSort.getBitVectorSize.toNat
      let x : Q(BitVec $w) ← reconstructTerm pf.getResult[0]![0]!
      let y : Q(BitVec $w) ← reconstructTerm pf.getResult[0]![1]!
      let z : Q(BitVec $w) ← reconstructTerm pf.getResult[1]!
      let h : Q((BitVec.adc' $x $y false).snd = $z) ← Meta.mkFreshExprMVar q((BitVec.adc' $x $y false).snd = $z)
      let mv ← Bool.boolify h.mvarId!
      let ds := [``BitVec.adc', ``BitVec.adcb', ``BitVec.iunfoldr, ``Fin.hIterate, ``Fin.hIterateFrom]
      let ts := [``BitVec.getLsb_cons, ``Nat.succ.injEq]
      let ps := [``Nat.reduceAdd, ``Nat.reduceLT, ``reduceDIte, ``reduceIte]
      let simpTheorems ← ds.foldrM (fun n a => a.addDeclToUnfold n) {}
      let simpTheorems ← ts.foldrM (fun n a => a.addConst n) simpTheorems
      let simpProcs ← ps.foldrM (fun n a => a.add n false) {}
      let (some mv, _) ← Meta.simpTarget mv { simpTheorems := #[simpTheorems] } simpProcs | throwError "simp failed"
      mv.refl
      addThm q($x + $y = $z) q(Eq.trans (BitVec.add_eq_adc' $x $y) $h)
    | _ => return none
  | _ => return none

end Smt.Reconstruct.BitVec
