/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Reconstruct.Prop.Core
import Smt.Reconstruct

namespace Smt.Reconstruct.BitVec

open Lean Qq

@[smt_sort_reconstruct] def reconstructBitVecSort : SortReconstructor := fun s => do match s.getKind with
  | .BITVECTOR_SORT =>
    let w : Nat := s.getBitVectorSize.val
    return q(Std.BitVec $w)
  | _             => return none

@[smt_term_reconstruct] partial def reconstructBitVec : TermReconstructor := fun t => do match t.getKind with
  | .CONST_BITVECTOR =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let v : Nat := (t.getBitVectorValue 10).toNat!
    return q(Std.BitVec.ofNat $w $v)
  | .BITVECTOR_BITOF =>
    let w : Nat := t[0]!.getSort.getBitVectorSize.val
    let x : Q(Std.BitVec $w) ← reconstructTerm t[0]!
    let i : Nat := t.getOp[0]!.getIntegerValue.toNat
    return q(«$x».getLsb $i = true)
  | .BITVECTOR_BB_TERM =>
    let w : Nat := t.getNumChildren
    let bs : Q(Std.BitVec 0) := q(.nil)
    let f (bs : Expr) (i : Nat) : ReconstructM Expr := do
      let p : Q(Prop) ← reconstructTerm t[i]!
      let bs : Q(Std.BitVec $i) := bs
      let hp : Q(Decidable $p) ← synthDecidableInst t[i]!
      return q(@Std.BitVec.cons $i (@decide $p $hp) $bs)
    let bs : Q(Std.BitVec $w) ← (List.range w).foldlM f bs
    return q($bs)
  | .BITVECTOR_ADD =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(Std.BitVec $w) ← reconstructTerm t[0]!
    let y : Q(Std.BitVec $w) ← reconstructTerm t[1]!
    return q($x + $y)
  | _ => return none
where
  rightAssocOpDecidableInst (op : Expr) (inst : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[t.getNumChildren - 1]!
    let mut currInst ← synthDecidableInst t[t.getNumChildren - 1]!
    for i in [1:t.getNumChildren] do
      let ct := t[t.getNumChildren - i - 1]!
      currInst := mkApp4 inst (← reconstructTerm ct) curr (← synthDecidableInst ct) currInst
      curr := mkApp2 op (← reconstructTerm ct) curr
    return currInst
  synthDecidableInst (t : cvc5.Term) : ReconstructM Expr := do match t.getKind with
    | .CONST_BOOLEAN => return if t.getBooleanValue then q(instDecidableTrue) else q(instDecidableFalse)
    | .NOT =>
      let p : Q(Prop) ← reconstructTerm t[0]!
      let hp : Q(Decidable $p) ← synthDecidableInst t[0]!
      return q(@instDecidableNot $p $hp)
    | .AND => rightAssocOpDecidableInst q(And) q(@instDecidableAnd) t
    | .OR => rightAssocOpDecidableInst q(Or) q(@instDecidableOr) t
    | .XOR => rightAssocOpDecidableInst q(XOr) q(@XOr.instDecidableXOr) t
    | .EQUAL =>
      if t[0]!.getSort.getKind == .BOOLEAN_SORT then
        let p : Q(Prop) ← reconstructTerm t[0]!
        let q : Q(Prop) ← reconstructTerm t[1]!
        let hp : Q(Decidable $p) ← synthDecidableInst t[0]!
        let hq : Q(Decidable $q) ← synthDecidableInst t[1]!
        return q(@instDecidableEqProp $p $q (@instDecidableIff $p $q $hp $hq))
      if t[0]!.getSort.getKind == .BITVECTOR_SORT then
        let w : Nat := t[0]!.getSort.getBitVectorSize.val
        return q(@Std.instDecidableEqBitVec $w)
      let p : Q(Prop) ← reconstructTerm t
      Meta.synthInstance q(Decidable $p)
    | .BITVECTOR_BITOF =>
      let w : Nat := t[0]!.getSort.getBitVectorSize.val
      let x : Q(Std.BitVec $w) ← reconstructTerm t[0]!
      let i : Nat := t.getOp[0]!.getIntegerValue.toNat
      return q(instDecidableEqBool («$x».getLsb $i) true)
    | _ =>
      let p : Q(Prop) ← reconstructTerm t
      Meta.synthInstance q(Decidable $p)

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match cvc5.RewriteRule.fromNat! pf.getArguments[0]!.getIntegerValue.toNat with
  | _ => return none

@[smt_proof_reconstruct] def reconstructBitVecProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE => reconstructRewrite pf
  | .BV_BITBLAST_STEP =>
    let t := pf.getArguments[0]![0]!
    match t.getKind with
    | .CONST_BITVECTOR =>
      let w : Nat := t.getSort.getBitVectorSize.toNat
      let t : Q(Std.BitVec $w) ← reconstructTerm pf.getResult[0]!
      let t' : Q(Std.BitVec $w) ← reconstructTerm pf.getResult[1]!
      addThm q($t = $t') q(Eq.refl $t)
    | _ => return none
  | _ => return none

end Smt.Reconstruct.BitVec
