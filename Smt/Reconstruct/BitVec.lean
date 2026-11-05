/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Smt.Reconstruct.Bool.Tactic
public meta import Smt.Reconstruct.Bool.Tactic
public import Smt.Reconstruct.BitVec.Bitblast
public meta import Smt.Reconstruct.BitVec.Bitblast
public import Smt.Reconstruct.BitVec.Core
public meta import Smt.Reconstruct.BitVec.Core
public import Smt.Reconstruct.BitVec.Rewrites
public meta import Smt.Reconstruct.BitVec.Rewrites
public import Smt.Reconstruct.BitVec.RewritesElimination
public meta import Smt.Reconstruct.BitVec.RewritesElimination
public import Smt.Reconstruct.BitVec.RewritesSimplification
public meta import Smt.Reconstruct.BitVec.RewritesSimplification
public import Smt.Reconstruct.Prop.Core
public meta import Smt.Reconstruct.Prop.Core
public import Smt.Reconstruct
public meta import Smt.Reconstruct

public meta section

namespace Smt.Reconstruct.BitVec

open Lean Qq

@[smt_sort_reconstruct] def reconstructBitVecSort : SortReconstructor := fun s => do match s.getKind! with
  | .BITVECTOR_SORT =>
    let w : Nat := s.getBitVectorSize!.toNat
    return q(BitVec $w)
  | _             => return none

partial def synthDecidableInst (t : cvc5.Term) : ReconstructM Expr := do match t.getKind! with
    | .CONST_BOOLEAN => return if t.getBooleanValue! then q(instDecidableTrue) else q(instDecidableFalse)
    | .NOT =>
      let p : Q(Prop) ← reconstructTerm t[0]!
      let hp : Q(Decidable $p) ← synthDecidableInst t[0]!
      return q(@instDecidableNot $p $hp)
    | .AND => rightAssocOpDecidableInst q(And) q(@instDecidableAnd) t
    | .OR => rightAssocOpDecidableInst q(Or) q(@instDecidableOr) t
    | .XOR => rightAssocOpDecidableInst q(XOr) q(@XOr.instDecidable) t
    | .EQUAL =>
      if t[0]!.getSort!.getKind! == .BOOLEAN_SORT then
        let p : Q(Prop) ← reconstructTerm t[0]!
        let q : Q(Prop) ← reconstructTerm t[1]!
        let hp : Q(Decidable $p) ← synthDecidableInst t[0]!
        let hq : Q(Decidable $q) ← synthDecidableInst t[1]!
        return q(@instDecidableEqOfIff $p $q (@instDecidableIff $p $q $hp $hq))
      if t[0]!.getSort!.getKind! == .BITVECTOR_SORT then
        let w : Nat := t[0]!.getSort!.getBitVectorSize!.toNat
        return q(@instDecidableEqBitVec $w)
      let p : Q(Prop) ← reconstructTerm t
      Meta.synthDecidableInstance q($p)
    | .BITVECTOR_BIT =>
      let w : Nat := t[0]!.getSort!.getBitVectorSize!.toNat
      let x : Q(BitVec $w) ← reconstructTerm t[0]!
      let i : Nat := t.getOp![0]!.getIntegerValue!.toNat
      return q(instDecidableEqBool («$x».getLsbD $i) true)
    | _ =>
      let p : Q(Prop) ← reconstructTerm t
      Meta.synthDecidableInstance q($p)
where
   rightAssocOpDecidableInst (op : Expr) (inst : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[t.getNumChildren - 1]!
    let mut currInst ← synthDecidableInst t[t.getNumChildren - 1]!
    for i in [1:t.getNumChildren] do
      let ct := t[t.getNumChildren - i - 1]!
      currInst := mkApp4 inst (← reconstructTerm ct) curr (← synthDecidableInst ct) currInst
      curr := mkApp2 op (← reconstructTerm ct) curr
    return currInst

@[smt_term_reconstruct] def reconstructBitVec : TermReconstructor := fun t => do match t.getKind! with
  | .CONST_BITVECTOR =>
    let w : Nat := t.getSort!.getBitVectorSize!.toNat
    let v : Nat := (t.getBitVectorValue! 10).toNat!
    return q(BitVec.ofNat $w $v)
  | .BITVECTOR_CONCAT =>
    let n : Nat := t.getNumChildren
    let w₁ : Nat := t[0]!.getSort!.getBitVectorSize!.toNat
    let a : Q(BitVec $w₁) ← reconstructTerm t[0]!
    let f := fun ⟨w₁, a⟩ t => do
      let w₂ : Nat ← pure t.getSort!.getBitVectorSize!.toNat
      let x : Q(BitVec $w₂) ← reconstructTerm t
      return ⟨q($w₁ + $w₂), q($a ++ $x)⟩
    let ⟨_, a⟩ ← t.getChildren[1:n].foldlM f (⟨q($w₁), a⟩ : Σ w : Q(Nat), Q(BitVec $w))
    return a
  | .BITVECTOR_AND =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    leftAssocOp q(@HAnd.hAnd (BitVec $w) (BitVec $w) (BitVec $w) _) t
  | .BITVECTOR_OR =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    leftAssocOp q(@HOr.hOr (BitVec $w) (BitVec $w) (BitVec $w) _) t
  | .BITVECTOR_XOR =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    leftAssocOp q(@HXor.hXor (BitVec $w) (BitVec $w) (BitVec $w) _) t
  | .BITVECTOR_NOT =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(~~~$x)
  | .BITVECTOR_MULT =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    leftAssocOp q(@HMul.hMul (BitVec $w) (BitVec $w) (BitVec $w) _) t
  | .BITVECTOR_ADD =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    leftAssocOp q(@HAdd.hAdd (BitVec $w) (BitVec $w) (BitVec $w) _) t
  | .BITVECTOR_SUB =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    leftAssocOp q(@HSub.hSub (BitVec $w) (BitVec $w) (BitVec $w) _) t
  | .BITVECTOR_NEG =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(-$x)
  | .BITVECTOR_UDIV =>
    let w : Nat := t.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.smtUDiv $x $y)
  | .BITVECTOR_UREM =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x % $y)
  | .BITVECTOR_SDIV =>
    let w : Nat := t.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.smtSDiv $x $y)
  | .BITVECTOR_SREM =>
    let w : Nat := t.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.srem $x $y)
  | .BITVECTOR_SMOD =>
    let w : Nat := t.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.smod $x $y)
  | .BITVECTOR_SHL =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x <<< $y)
  | .BITVECTOR_LSHR =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x >>> $y)
  | .BITVECTOR_ASHR =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.sshiftRight' $x $y)
  | .BITVECTOR_ULT =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x < $y)
  | .BITVECTOR_ULE =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x ≤ $y)
  | .BITVECTOR_UGT =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x > $y)
  | .BITVECTOR_UGE =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q($x ≥ $y)
  | .BITVECTOR_SLT =>
    let w : Nat := t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.slt $x $y = true)
  | .BITVECTOR_SLE =>
    let w : Nat := t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.sle $x $y = true)
  | .BITVECTOR_EXTRACT =>
    let w : Nat := t[0]!.getSort!.getBitVectorSize!.toNat
    let i : Nat := t.getOp![0]!.getIntegerValue!.toNat
    let j : Nat := t.getOp![1]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».extractLsb $i $j)
  | .BITVECTOR_REPEAT =>
    let w : Nat := t[0]!.getSort!.getBitVectorSize!.toNat
    let n : Nat := t.getOp![0]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».replicate $n)
  | .BITVECTOR_ZERO_EXTEND =>
    let w : Nat := t[0]!.getSort!.getBitVectorSize!.toNat
    let n : Nat := t.getOp![0]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».zeroExtend ($w + $n))
  | .BITVECTOR_SIGN_EXTEND =>
    let w : Nat := t[0]!.getSort!.getBitVectorSize!.toNat
    let n : Nat := t.getOp![0]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».signExtend ($w + $n))
  | .BITVECTOR_ROTATE_LEFT =>
    let w : Nat := t.getSort!.getBitVectorSize!.toNat
    let n : Nat := t.getOp![0]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».rotateLeft $n)
  | .BITVECTOR_ROTATE_RIGHT =>
    let w : Nat := t.getSort!.getBitVectorSize!.toNat
    let n : Nat := t.getOp![0]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(«$x».rotateRight $n)
  | .INT_TO_BITVECTOR =>
    let w : Nat := t.getSort!.getBitVectorSize!.toNat
    let x : Q(Int) ← reconstructTerm t[0]!
    return q(BitVec.ofInt $w $x)
  | .BITVECTOR_UBV_TO_INT =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q((«$x».toNat : Int))
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
    let w : Nat := t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let i : Nat := t.getOp![0]!.getIntegerValue!.toNat
    return q(«$x».getLsbD $i = true)
  | .BITVECTOR_ITE =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    let c : Q(BitVec 1) ← reconstructTerm t[0]!
    let x : Q(BitVec $w) ← reconstructTerm t[1]!
    let y : Q(BitVec $w) ← reconstructTerm t[2]!
    return q(BitVec.smtIte $c $x $y)
  | .BITVECTOR_COMP =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.smtComp $x $y)
  | .BITVECTOR_NAND =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.smtNand $x $y)
  | .BITVECTOR_NOR =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.smtNor $x $y)
  | .BITVECTOR_XNOR =>
    let w : Nat ← pure t.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.smtXnor $x $y)
  | .BITVECTOR_SGT =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.slt $y $x = true)
  | .BITVECTOR_SGE =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.sle $y $x = true)
  | .BITVECTOR_REDOR =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(BitVec.smtRedor $x)
  | .BITVECTOR_REDAND =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(BitVec.smtRedand $x)
  | .BITVECTOR_UADDO =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.uaddOverflow $x $y = true)
  | .BITVECTOR_SADDO =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.saddOverflow $x $y = true)
  | .BITVECTOR_UMULO =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.umulOverflow $x $y = true)
  | .BITVECTOR_SMULO =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.smulOverflow $x $y = true)
  | .BITVECTOR_USUBO =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.usubOverflow $x $y = true)
  | .BITVECTOR_SSUBO =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.ssubOverflow $x $y = true)
  | .BITVECTOR_SDIVO =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    let y : Q(BitVec $w) ← reconstructTerm t[1]!
    return q(BitVec.sdivOverflow $x $y = true)
  | .BITVECTOR_NEGO =>
    let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t[0]!
    return q(BitVec.negOverflow $x = true)
  | .INTERNAL_KIND => reconstructSymbolic t
  | _ => return none
where
  leftAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op curr (← reconstructTerm t[i]!)
    return curr
  /-- Instances of RARE rules contain indexed operators with symbolic indices, e.g.
  `(extract 7 5 x)`, symbolic constants `(@bv 5 8)`, and `(@bvsize x)`. Their kinds are internal to
  cvc5, so they are recognized by their head symbol. The indices come first among their children.
  They are reconstructed like their concrete counterparts (e.g. `((_ extract 7 5) x)`). -/
  reconstructSymbolic (t : cvc5.Term) : ReconstructM (Option Expr) := do
    let index? (i : Nat) : Option Nat :=
      let c := t[i]!
      if c.getKind! == .CONST_INTEGER && c.getIntegerValue! ≥ 0 then
        some c.getIntegerValue!.toNat
      else
        none
    let head := String.ofList ((t.toString.toList.drop 1).takeWhile (· != ' '))
    match head, t.getNumChildren with
    | "extract", 3 =>
      let (some i, some j) := (index? 0, index? 1) | return none
      let w : Nat ← pure t[2]!.getSort!.getBitVectorSize!.toNat
      let x : Q(BitVec $w) ← reconstructTerm t[2]!
      return q(«$x».extractLsb $i $j)
    | "repeat", 2 =>
      let some n := index? 0 | return none
      let w : Nat ← pure t[1]!.getSort!.getBitVectorSize!.toNat
      let x : Q(BitVec $w) ← reconstructTerm t[1]!
      return q(«$x».replicate $n)
    | "zero_extend", 2 =>
      let some n := index? 0 | return none
      let w : Nat ← pure t[1]!.getSort!.getBitVectorSize!.toNat
      let x : Q(BitVec $w) ← reconstructTerm t[1]!
      return q(«$x».zeroExtend ($w + $n))
    | "sign_extend", 2 =>
      let some n := index? 0 | return none
      let w : Nat ← pure t[1]!.getSort!.getBitVectorSize!.toNat
      let x : Q(BitVec $w) ← reconstructTerm t[1]!
      return q(«$x».signExtend ($w + $n))
    | "rotate_left", 2 =>
      let some n := index? 0 | return none
      let w : Nat ← pure t[1]!.getSort!.getBitVectorSize!.toNat
      let x : Q(BitVec $w) ← reconstructTerm t[1]!
      return q(«$x».rotateLeft $n)
    | "rotate_right", 2 =>
      let some n := index? 0 | return none
      let w : Nat ← pure t[1]!.getSort!.getBitVectorSize!.toNat
      let x : Q(BitVec $w) ← reconstructTerm t[1]!
      return q(«$x».rotateRight $n)
    | "@bv", 2 =>
      let some w := index? 1 | return none
      if let some n := index? 0 then
        return q(BitVec.ofNat $w $n)
      let n : Q(Int) ← reconstructTerm t[0]!
      return q(BitVec.ofNat $w «$n».toNat)
    | "@bvsize", 1 =>
      let w : Q(Nat) := mkRawNatLit t[0]!.getSort!.getBitVectorSize!.toNat
      return q((OfNat.ofNat $w : Int))
    | _, _ => return none

/-! ### RARE rewrites

Each rewrite rule `bv-foo-bar` is proved by the theorem `Rewrite.foo_bar`. Its binders are
instantiated by name from the arguments of the `DSL_REWRITE` step, which are the rule's parameters
in declaration order. Width binders are determined by unification. The remaining hypotheses are
closed propositions about numerals, proved by evaluation in the kernel. -/

/-- The theorem proving each bit-vector RARE rule, and the rule's parameters in declaration order
(the order of the arguments of `DSL_REWRITE` steps). -/
def rewriteInfo? : cvc5.ProofRewriteRule → Option (Name × Array String)
  | .BV_CONCAT_EXTRACT_MERGE =>
    some (``Rewrite.concat_extract_merge, #["xs", "s", "ys", "i", "j", "j1", "k"])
  | .BV_EXTRACT_EXTRACT => some (``Rewrite.extract_extract, #["x", "i", "j", "k", "l", "ll", "kk"])
  | .BV_EXTRACT_WHOLE => some (``Rewrite.extract_whole, #["x", "n"])
  | .BV_EXTRACT_CONCAT_1 => some (``Rewrite.extract_concat_1, #["x", "xs", "y", "i", "j"])
  | .BV_EXTRACT_CONCAT_2 =>
    some (``Rewrite.extract_concat_2, #["x", "xs", "y", "i", "j", "u1", "u2"])
  | .BV_EXTRACT_CONCAT_3 =>
    some (``Rewrite.extract_concat_3, #["x", "y", "xs", "i", "j", "u2", "l2"])
  | .BV_EXTRACT_CONCAT_4 => some (``Rewrite.extract_concat_4, #["x", "y", "xs", "i", "j"])
  | .BV_EQ_EXTRACT_ELIM1 =>
    some (``Rewrite.eq_extract_elim1, #["x", "y", "i", "j", "wm1", "jp1", "im1"])
  | .BV_EQ_EXTRACT_ELIM2 => some (``Rewrite.eq_extract_elim2, #["x", "y", "j", "wm1", "jp1"])
  | .BV_EQ_EXTRACT_ELIM3 => some (``Rewrite.eq_extract_elim3, #["x", "y", "i", "j", "im1"])
  | .BV_EXTRACT_NOT => some (``Rewrite.extract_not, #["x", "i", "j"])
  | .BV_EXTRACT_SIGN_EXTEND_1 => some (``Rewrite.extract_sign_extend_1, #["x", "low", "high", "k"])
  | .BV_EXTRACT_SIGN_EXTEND_2 =>
    some (``Rewrite.extract_sign_extend_2, #["x", "low", "high", "k", "nm1", "sn"])
  | .BV_EXTRACT_SIGN_EXTEND_3 =>
    some (``Rewrite.extract_sign_extend_3, #["x", "low", "high", "k", "rn", "nm1"])
  | .BV_NOT_XOR => some (``Rewrite.not_xor, #["x1", "x2", "xs"])
  | .BV_AND_SIMPLIFY_1 => some (``Rewrite.and_simplify_1, #["xs", "ys", "zs", "x", "w"])
  | .BV_AND_SIMPLIFY_2 => some (``Rewrite.and_simplify_2, #["xs", "ys", "zs", "x", "w"])
  | .BV_OR_SIMPLIFY_1 => some (``Rewrite.or_simplify_1, #["xs", "ys", "zs", "x", "w"])
  | .BV_OR_SIMPLIFY_2 => some (``Rewrite.or_simplify_2, #["xs", "ys", "zs", "x", "w"])
  | .BV_XOR_SIMPLIFY_1 => some (``Rewrite.xor_simplify_1, #["xs", "ys", "zs", "x"])
  | .BV_XOR_SIMPLIFY_2 => some (``Rewrite.xor_simplify_2, #["xs", "ys", "zs", "x"])
  | .BV_XOR_SIMPLIFY_3 => some (``Rewrite.xor_simplify_3, #["xs", "ys", "zs", "x"])
  | .BV_ULT_ADD_ONE => some (``Rewrite.ult_add_one, #["x", "ys", "zs", "c1", "w"])
  | .BV_MULT_SLT_MULT_1 => some (``Rewrite.mult_slt_mult_1, #["x", "y", "a", "n", "m", "tn", "an"])
  | .BV_MULT_SLT_MULT_2 => some (``Rewrite.mult_slt_mult_2, #["x", "y", "a", "n", "m", "tn", "an"])
  | .BV_COMMUTATIVE_XOR => some (``Rewrite.commutative_xor, #["x", "y"])
  | .BV_COMMUTATIVE_COMP => some (``Rewrite.commutative_comp, #["x", "y"])
  | .BV_ZERO_EXTEND_ELIMINATE_0 => some (``Rewrite.zero_extend_eliminate_0, #["x"])
  | .BV_SIGN_EXTEND_ELIMINATE_0 => some (``Rewrite.sign_extend_eliminate_0, #["x"])
  | .BV_NOT_NEQ => some (``Rewrite.not_neq, #["x"])
  | .BV_ULT_ONES => some (``Rewrite.ult_ones, #["x", "n", "w"])
  | .BV_CONCAT_MERGE_CONST =>
    some (``Rewrite.concat_merge_const, #["xs", "n1", "w1", "n2", "w2", "ww", "zs"])
  | .BV_COMMUTATIVE_ADD => some (``Rewrite.commutative_add, #["x", "y"])
  | .BV_SUB_ELIMINATE => some (``Rewrite.sub_eliminate, #["x", "y"])
  | .BV_ITE_WIDTH_ONE => some (``Rewrite.ite_width_one, #["x"])
  | .BV_ITE_WIDTH_ONE_NOT => some (``Rewrite.ite_width_one_not, #["x"])
  | .BV_EQ_XOR_SOLVE => some (``Rewrite.eq_xor_solve, #["x", "y", "z"])
  | .BV_EQ_NOT_SOLVE => some (``Rewrite.eq_not_solve, #["x", "y"])
  | .BV_UGT_ELIMINATE => some (``Rewrite.ugt_eliminate, #["x", "y"])
  | .BV_UGE_ELIMINATE => some (``Rewrite.uge_eliminate, #["x", "y"])
  | .BV_SGT_ELIMINATE => some (``Rewrite.sgt_eliminate, #["x", "y"])
  | .BV_SGE_ELIMINATE => some (``Rewrite.sge_eliminate, #["x", "y"])
  | .BV_SLE_ELIMINATE => some (``Rewrite.sle_eliminate, #["x", "y"])
  | .BV_REDOR_ELIMINATE => some (``Rewrite.redor_eliminate, #["x", "w"])
  | .BV_REDAND_ELIMINATE => some (``Rewrite.redand_eliminate, #["x", "w"])
  | .BV_ULE_ELIMINATE => some (``Rewrite.ule_eliminate, #["x", "y"])
  | .BV_COMP_ELIMINATE => some (``Rewrite.comp_eliminate, #["x", "y"])
  | .BV_ROTATE_LEFT_ELIMINATE_1 =>
    some (``Rewrite.rotate_left_eliminate_1, #["x", "amount", "u1", "u2", "l2"])
  | .BV_ROTATE_LEFT_ELIMINATE_2 => some (``Rewrite.rotate_left_eliminate_2, #["x", "amount"])
  | .BV_ROTATE_RIGHT_ELIMINATE_1 =>
    some (``Rewrite.rotate_right_eliminate_1, #["x", "amount", "u1", "u2", "l2"])
  | .BV_ROTATE_RIGHT_ELIMINATE_2 => some (``Rewrite.rotate_right_eliminate_2, #["x", "amount"])
  | .BV_NAND_ELIMINATE => some (``Rewrite.nand_eliminate, #["x", "y"])
  | .BV_NOR_ELIMINATE => some (``Rewrite.nor_eliminate, #["x", "y"])
  | .BV_XNOR_ELIMINATE => some (``Rewrite.xnor_eliminate, #["x", "y"])
  | .BV_SDIV_ELIMINATE => some (``Rewrite.sdiv_eliminate, #["x", "y", "nm1"])
  | .BV_ZERO_EXTEND_ELIMINATE => some (``Rewrite.zero_extend_eliminate, #["x", "n"])
  | .BV_UADDO_ELIMINATE => some (``Rewrite.uaddo_eliminate, #["x", "y", "w"])
  | .BV_SADDO_ELIMINATE => some (``Rewrite.saddo_eliminate, #["x", "y", "wm1"])
  | .BV_SDIVO_ELIMINATE => some (``Rewrite.sdivo_eliminate, #["x", "y", "w", "wm1"])
  | .BV_SMOD_ELIMINATE => some (``Rewrite.smod_eliminate, #["x", "y", "w", "wm1"])
  | .BV_SREM_ELIMINATE => some (``Rewrite.srem_eliminate, #["x", "y", "nm1"])
  | .BV_USUBO_ELIMINATE => some (``Rewrite.usubo_eliminate, #["x", "y", "n"])
  | .BV_SSUBO_ELIMINATE => some (``Rewrite.ssubo_eliminate, #["x", "y", "nm1"])
  | .BV_NEGO_ELIMINATE => some (``Rewrite.nego_eliminate, #["x", "n"])
  | .BV_ITE_EQUAL_CHILDREN => some (``Rewrite.ite_equal_children, #["c", "x"])
  | .BV_ITE_CONST_CHILDREN_1 => some (``Rewrite.ite_const_children_1, #["c"])
  | .BV_ITE_CONST_CHILDREN_2 => some (``Rewrite.ite_const_children_2, #["c"])
  | .BV_ITE_EQUAL_COND_1 => some (``Rewrite.ite_equal_cond_1, #["c0", "t0", "e0", "e1"])
  | .BV_ITE_EQUAL_COND_2 => some (``Rewrite.ite_equal_cond_2, #["c0", "t0", "t1", "e1"])
  | .BV_ITE_EQUAL_COND_3 => some (``Rewrite.ite_equal_cond_3, #["c0", "t0", "e0", "t1", "e1"])
  | .BV_ITE_MERGE_THEN_IF => some (``Rewrite.ite_merge_then_if, #["c0", "c1", "t1", "e1"])
  | .BV_ITE_MERGE_ELSE_IF => some (``Rewrite.ite_merge_else_if, #["c0", "c1", "t1", "e1"])
  | .BV_ITE_MERGE_THEN_ELSE => some (``Rewrite.ite_merge_then_else, #["c0", "c1", "t0", "e1"])
  | .BV_ITE_MERGE_ELSE_ELSE => some (``Rewrite.ite_merge_else_else, #["c0", "c1", "t1", "t0"])
  | .BV_SHL_BY_CONST_0 => some (``Rewrite.shl_by_const_0, #["x", "sz"])
  | .BV_SHL_BY_CONST_1 => some (``Rewrite.shl_by_const_1, #["x", "amount", "sz", "en"])
  | .BV_SHL_BY_CONST_2 => some (``Rewrite.shl_by_const_2, #["x", "amount", "sz", "w"])
  | .BV_LSHR_BY_CONST_0 => some (``Rewrite.lshr_by_const_0, #["x", "sz"])
  | .BV_LSHR_BY_CONST_1 => some (``Rewrite.lshr_by_const_1, #["x", "amount", "sz", "nm1"])
  | .BV_LSHR_BY_CONST_2 => some (``Rewrite.lshr_by_const_2, #["x", "amount", "sz"])
  | .BV_ASHR_BY_CONST_0 => some (``Rewrite.ashr_by_const_0, #["x", "sz"])
  | .BV_ASHR_BY_CONST_1 => some (``Rewrite.ashr_by_const_1, #["x", "amount", "sz", "nm1"])
  | .BV_ASHR_BY_CONST_2 => some (``Rewrite.ashr_by_const_2, #["x", "amount", "sz", "nm1", "rn"])
  | .BV_AND_CONCAT_PULLUP =>
    some (``Rewrite.and_concat_pullup, #["xs", "ws", "y", "z", "ys", "nxm1", "ny", "nym1"])
  | .BV_OR_CONCAT_PULLUP =>
    some (``Rewrite.or_concat_pullup, #["xs", "ws", "y", "z", "ys", "nxm1", "ny", "nym1"])
  | .BV_XOR_CONCAT_PULLUP =>
    some (``Rewrite.xor_concat_pullup, #["xs", "ws", "y", "z", "ys", "nxm1", "ny", "nym1"])
  | .BV_AND_CONCAT_PULLUP2 =>
    some (``Rewrite.and_concat_pullup2, #["xs", "ws", "y", "z", "ys", "nxm1", "ny", "nym1"])
  | .BV_OR_CONCAT_PULLUP2 =>
    some (``Rewrite.or_concat_pullup2, #["xs", "ws", "y", "z", "ys", "nxm1", "ny", "nym1"])
  | .BV_XOR_CONCAT_PULLUP2 =>
    some (``Rewrite.xor_concat_pullup2, #["xs", "ws", "y", "z", "ys", "nxm1", "ny", "nym1"])
  | .BV_AND_CONCAT_PULLUP3 =>
    some (``Rewrite.and_concat_pullup3,
      #["xs", "ws", "y", "z", "u", "nxm1", "nyu", "nyum1", "nu", "num1"])
  | .BV_OR_CONCAT_PULLUP3 =>
    some (``Rewrite.or_concat_pullup3,
      #["xs", "ws", "y", "z", "u", "nxm1", "nyu", "nyum1", "nu", "num1"])
  | .BV_XOR_CONCAT_PULLUP3 =>
    some (``Rewrite.xor_concat_pullup3,
      #["xs", "ws", "y", "z", "u", "nxm1", "nyu", "nyum1", "nu", "num1"])
  | .BV_XOR_DUPLICATE => some (``Rewrite.xor_duplicate, #["x", "w"])
  | .BV_XOR_ONES => some (``Rewrite.xor_ones, #["xs", "zs", "n", "w"])
  | .BV_XOR_NOT => some (``Rewrite.xor_not, #["x", "y"])
  | .BV_NOT_IDEMP => some (``Rewrite.not_idemp, #["x"])
  | .BV_ULT_ZERO_1 => some (``Rewrite.ult_zero_1, #["x", "n"])
  | .BV_ULT_ZERO_2 => some (``Rewrite.ult_zero_2, #["x", "n"])
  | .BV_ULT_SELF => some (``Rewrite.ult_self, #["x"])
  | .BV_LT_SELF => some (``Rewrite.lt_self, #["x"])
  | .BV_ULE_SELF => some (``Rewrite.ule_self, #["x"])
  | .BV_ULE_ZERO => some (``Rewrite.ule_zero, #["x", "n"])
  | .BV_ZERO_ULE => some (``Rewrite.zero_ule, #["x", "n"])
  | .BV_SLE_SELF => some (``Rewrite.sle_self, #["x"])
  | .BV_ULE_MAX => some (``Rewrite.ule_max, #["x", "n", "w"])
  | .BV_NOT_ULT => some (``Rewrite.not_ult, #["x", "y"])
  | .BV_MULT_POW2_1 =>
    some (``Rewrite.mult_pow2_1, #["xs", "ys", "z", "size", "n", "exponent", "u"])
  | .BV_MULT_POW2_2 =>
    some (``Rewrite.mult_pow2_2, #["xs", "ys", "z", "size", "n", "exponent", "u"])
  | .BV_MULT_POW2_2B => some (``Rewrite.mult_pow2_2b, #["z", "size", "n", "exponent", "u"])
  | .BV_EXTRACT_MULT_LEADING_BIT =>
    some (``Rewrite.extract_mult_leading_bit,
      #["high", "low", "x1i", "x1in", "x2", "y1i", "y1in", "y2", "w"])
  | .BV_UDIV_POW2_NOT_ONE => some (``Rewrite.udiv_pow2_not_one, #["x", "v", "n", "power", "nm1"])
  | .BV_UDIV_ZERO => some (``Rewrite.udiv_zero, #["x", "n"])
  | .BV_UDIV_ONE => some (``Rewrite.udiv_one, #["x", "n"])
  | .BV_UREM_POW2_NOT_ONE => some (``Rewrite.urem_pow2_not_one, #["x", "v", "n", "nmp", "pm1"])
  | .BV_UREM_ONE => some (``Rewrite.urem_one, #["x", "n"])
  | .BV_UREM_SELF => some (``Rewrite.urem_self, #["x", "w"])
  | .BV_SHL_ZERO => some (``Rewrite.shl_zero, #["a", "n"])
  | .BV_LSHR_ZERO => some (``Rewrite.lshr_zero, #["a", "n"])
  | .BV_ASHR_ZERO => some (``Rewrite.ashr_zero, #["a", "n"])
  | .BV_UGT_UREM => some (``Rewrite.ugt_urem, #["y", "x", "w"])
  | .BV_ULT_ONE => some (``Rewrite.ult_one, #["x", "n"])
  | .BV_MERGE_SIGN_EXTEND_1 => some (``Rewrite.merge_sign_extend_1, #["x", "i", "j", "k"])
  | .BV_MERGE_SIGN_EXTEND_2 => some (``Rewrite.merge_sign_extend_2, #["x", "i", "j", "k"])
  | .BV_SIGN_EXTEND_EQ_CONST_1 =>
    some (``Rewrite.sign_extend_eq_const_1, #["x", "m", "c", "nm", "mp1", "nm1", "nmm1"])
  | .BV_SIGN_EXTEND_EQ_CONST_2 =>
    some (``Rewrite.sign_extend_eq_const_2, #["x", "m", "c", "nm", "mp1", "nm1", "nmm1"])
  | .BV_ZERO_EXTEND_EQ_CONST_1 =>
    some (``Rewrite.zero_extend_eq_const_1, #["x", "m", "c", "nm", "nm1", "nmm1"])
  | .BV_ZERO_EXTEND_EQ_CONST_2 =>
    some (``Rewrite.zero_extend_eq_const_2, #["x", "m", "c", "nm", "nm1", "nmm1"])
  | .BV_ZERO_EXTEND_ULT_CONST_1 =>
    some (``Rewrite.zero_extend_ult_const_1, #["x", "m", "c", "nm", "nm1"])
  | .BV_ZERO_EXTEND_ULT_CONST_2 =>
    some (``Rewrite.zero_extend_ult_const_2, #["x", "m", "c", "nm", "nm1"])
  | .BV_SIGN_EXTEND_ULT_CONST_1 =>
    some (``Rewrite.sign_extend_ult_const_1, #["x", "m", "c", "nm", "nm1"])
  | .BV_SIGN_EXTEND_ULT_CONST_2 =>
    some (``Rewrite.sign_extend_ult_const_2, #["x", "m", "c", "nm", "nm1"])
  | .BV_SIGN_EXTEND_ULT_CONST_3 =>
    some (``Rewrite.sign_extend_ult_const_3, #["x", "m", "c", "nm", "nm1"])
  | .BV_SIGN_EXTEND_ULT_CONST_4 =>
    some (``Rewrite.sign_extend_ult_const_4, #["x", "m", "c", "nm", "nm1"])
  | _ => none

open Meta in
/-- Reconstruct the argument `t` of a rewrite step for a theorem binder of type `ty`. -/
def reconstructRuleArg (ty : Expr) (t : cvc5.Term) : ReconstructM (Option Expr) := do
  let ty ← whnfR (← instantiateMVars ty)
  if ty.isConstOf ``Nat then
    unless t.getKind! == .CONST_INTEGER && t.getIntegerValue! ≥ 0 do return none
    return some (mkNatLit t.getIntegerValue!.toNat)
  if ty.isAppOfArity ``BitVec 1 then
    return some (← reconstructTerm t)
  if ty.isConstOf ``HBitVecList then
    let mut xs := mkConst ``HBitVecList.nil
    for c in t.getChildren.reverse do
      let w : Nat := c.getSort!.getBitVectorSize!.toNat
      xs := mkApp3 (mkConst ``HBitVecList.cons) (mkNatLit w) (← reconstructTerm c) xs
    return some xs
  if ty.isAppOfArity ``List 1 then
    let α := ty.appArg!
    let mut xs := mkApp (mkConst ``List.nil [Level.zero]) α
    for c in t.getChildren.reverse do
      let x ← reconstructTerm c
      unless ← isDefEq α (← inferType x) do return none
      xs := mkApp3 (mkConst ``List.cons [Level.zero]) α x xs
    return some xs
  return none

open Meta in
/-- A proof of the closed decidable proposition `p` by evaluation in the kernel, if `p` holds.
`p` is evaluated at the meta level first, so that a false side condition fails here instead of in
the kernel. -/
def decideProof? (p : Expr) : MetaM (Option Expr) := do
  let some inst ← (try synthInstance? (mkApp (mkConst ``Decidable) p) catch _ => pure none)
    | return none
  if inst.getUsedConstants.any (isNoncomputable (← getEnv)) then return none
  let r ← try withAtLeastTransparency .default <| whnf (mkApp2 (mkConst ``Decidable.decide) p inst)
    catch _ => return none
  unless r.isConstOf ``true do return none
  let h := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``true)
  return some (mkApp3 (mkConst ``of_decide_eq_true) p inst h)

open Meta in
/-- A proof of `Nat.log2 e = k`, where the closed term `e` evaluates to `n` and `k` is the numeral
`n.log2`. -/
def log2Eq? (e : Expr) (n : Nat) : MetaM (Option Expr) := do
  if n == 0 then
    let some h ← decideProof? (← mkEq e (mkNatLit 0)) | return none
    return some (← mkEqTrans (← mkCongrArg (mkConst ``Nat.log2) h) (mkConst ``Nat.log2_zero))
  let some hne ← decideProof? (mkNot (← mkEq e (mkNatLit 0))) | return none
  let iff := mkApp3 (mkConst ``Nat.log2_eq_iff) e (mkNatLit n.log2) hne
  let some (a, b) := (← inferType iff).iff? | return none
  let some (b₁, b₂) := b.and? | return none
  let some h₁ ← decideProof? b₁ | return none
  let some h₂ ← decideProof? b₂ | return none
  return some (mkApp4 (mkConst ``Iff.mpr) a b iff (mkApp4 (mkConst ``And.intro) b₁ b₂ h₁ h₂))

open Meta in
/-- `Nat.log2` is defined by well-founded recursion, which the kernel cannot evaluate on large
numerals (memory explodes). Replace an occurrence `Nat.log2 e` in the proposition `p` by its value,
computed natively. Returns the new proposition and a proof that `p` equals it. -/
def elimLog2? (p : Expr) : MetaM (Option (Expr × Expr)) := do
  let some l := p.find? (·.isAppOfArity ``Nat.log2 1) | return none
  let some n ← (evalNat l.appArg!).run | return none
  let some h ← log2Eq? l.appArg! n | return none
  let motive := Expr.lam `z (mkConst ``Nat) (← kabstract p l) .default
  unless ← isTypeCorrect motive do return none
  return some (motive.beta #[mkNatLit n.log2], ← mkCongrArg motive h)

open Meta in
/-- Prove the hypothesis `p` of a rewrite theorem by evaluation. `p` may be in the forms cvc5 uses
for side conditions: `q = True`, `q = False`, or `a = b`. -/
partial def proveSideCondition? (p : Expr) : MetaM (Option Expr) := do
  if let some (α, q, b) := p.eq? then
    if α.isProp && b.isConstOf ``True then
      let some h ← proveSideCondition? q | return none
      return some (mkApp2 (mkConst ``eq_true) q h)
    if α.isProp && b.isConstOf ``False then
      let some h ← proveSideCondition? (mkNot q) | return none
      return some (mkApp2 (mkConst ``eq_false) q h)
  if let some (p', hp) ← elimLog2? p then
    let some h ← proveSideCondition? p' | return none
    return some (← mkEqMPR hp h)
  decideProof? p

open Meta in
/-- Instantiate the theorem `thm` with the arguments of a rewrite step, given with the names of the
rule's parameters, and prove its hypotheses. -/
def instantiateRewrite? (thm : Name) (args : Array (String × cvc5.Term)) :
    ReconstructM (Option Expr) := do
  let c := mkConst thm
  let type ← inferType c
  let (mvs, _, _) ← forallMetaTelescope type
  -- The rule's parameters. Binders of substituted parameters are absent and are skipped. Lists of
  -- bit-vectors come last, because the widths of their elements are determined by the others.
  for lists in [false, true] do
    for (n, mv) in type.getForallBinderNames.zip mvs.toList do
      if ← mv.mvarId!.isAssigned then continue
      let ty ← whnfR (← instantiateMVars (← inferType mv))
      if (← isProp ty) || ty.isAppOfArity ``List 1 != lists then continue
      let some (_, t) := args.find? (·.1 == n.toString) | continue
      let some v ← reconstructRuleArg ty t | return none
      unless ← isDefEq ty (← inferType v) do return none
      mv.mvarId!.assign v
  -- The widths are now determined by unification, and the hypotheses are closed.
  for mv in mvs do
    if ← mv.mvarId!.isAssigned then continue
    let ty ← instantiateMVars (← inferType mv)
    unless ← isProp ty do return none
    if ty.hasMVar then return none
    let some h ← proveSideCondition? ty | return none
    mv.mvarId!.assign h
  return some (← instantiateMVars (mkAppN c mvs))

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let .ok rule := pf.getRewriteRule | return none
  let some (thm, params) := rewriteInfo? rule | return none
  let args := pf.getArguments
  if args.size != params.size + 1 then return none
  let some h ← instantiateRewrite? thm (params.zip (args.extract 1 args.size)) | return none
  addThm (← reconstructTerm pf.getResult) h

@[smt_proof_reconstruct] def reconstructBitVecProof : ProofReconstructor := fun pf => do match pf.getRule with
  | .DSL_REWRITE => reconstructRewrite pf
  | .BV_BITBLAST_STEP =>
    let t := pf.getArguments[0]![0]!
    match t.getKind! with
    | .CONST_BITVECTOR =>
      let w : Nat := t.getSort!.getBitVectorSize!.toNat
      let t : Q(BitVec $w) ← reconstructTerm pf.getResult[0]!
      let t' : Q(BitVec $w) ← reconstructTerm pf.getResult[1]!
      addThm q($t = $t') q(Eq.refl $t)
    | .CONSTANT =>
      let w : Nat := t.getSort!.getBitVectorSize!.toNat
      let x : Q(BitVec $w) ← reconstructTerm pf.getResult[0]!
      let x' : Q(BitVec $w) ← reconstructTerm pf.getResult[1]!
      let h : Q(«$x».bb = $x') ← Meta.mkFreshExprMVar q(«$x».bb = $x')
      let mv ← Bool.boolify h.mvarId!
      let ds := [``BitVec.bb, ``BitVec.iunfoldr, ``Fin.hIterate, ``Fin.hIterateFrom]
      let ps := [``Nat.reduceAdd, ``Nat.reduceLT, ``reduceDIte]
      let simpTheorems ← ds.foldrM (fun n a => a.addDeclToUnfold n) {}
      let simpProcs ← ps.foldrM (fun n a => a.add n false) {}
      let ctx ← Meta.Simp.mkContext {} #[simpTheorems]
      let (some mv, _) ← Meta.simpTarget mv ctx simpProcs | throwError "simp failed"
      mv.refl
      addThm q($x = $x') q(Eq.trans (BitVec.self_eq_bb $x) $h)
    | .EQUAL =>
      let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
      let x : Q(BitVec $w) ← reconstructTerm pf.getResult[0]![0]!
      let y : Q(BitVec $w) ← reconstructTerm pf.getResult[0]![1]!
      let p : Q(Prop) ← reconstructTerm pf.getResult[1]!
      let hp : Q(Decidable $p) ← synthDecidableInst pf.getResult[1]!
      let h : Q(decide (BitVec.beq $x $y) = decide $p) ← Meta.mkFreshExprMVar q(decide (BitVec.beq $x $y) = @decide $p $hp)
      let mv ← Bool.boolify h.mvarId!
      let ds := [``BitVec.beq, ``BitVec.beq.go]
      let ts := [``BitVec.getLsbD_cons, ``Nat.succ.injEq]
      let ps := [``Nat.reduceAdd, ``Nat.reduceSub, ``Nat.reduceEqDiff, ``reduceIte]
      let simpTheorems ← ds.foldrM (fun n a => a.addDeclToUnfold n) {}
      let simpTheorems ← ts.foldrM (fun n a => a.addConst n) simpTheorems
      let ctx ← Meta.Simp.mkContext {} #[simpTheorems]
      let simpProcs ← ps.foldrM (fun n a => a.add n false) {}
      let (some mv, _) ← Meta.simpTarget mv ctx simpProcs | throwError "simp failed"
      mv.refl
      addThm q(($x = $y) = $p) q(Eq.trans (BitVec.eq_eq_beq $x $y) (Bool.eq_of_decide_eq $h))
    | .BITVECTOR_ADD =>
      let w : Nat ← pure t[0]!.getSort!.getBitVectorSize!.toNat
      let x : Q(BitVec $w) ← reconstructTerm pf.getResult[0]![0]!
      let y : Q(BitVec $w) ← reconstructTerm pf.getResult[0]![1]!
      let z : Q(BitVec $w) ← reconstructTerm pf.getResult[1]!
      let h : Q((BitVec.adc' $x $y false).snd = $z) ← Meta.mkFreshExprMVar q((BitVec.adc' $x $y false).snd = $z)
      let mv ← Bool.boolify h.mvarId!
      let ds := [``BitVec.adc', ``BitVec.adcb', ``BitVec.iunfoldr, ``Fin.hIterate, ``Fin.hIterateFrom]
      let ts := [``BitVec.getLsbD_cons, ``Nat.succ.injEq]
      let ps := [``Nat.reduceAdd, ``Nat.reduceLT, ``reduceDIte, ``reduceIte]
      let simpTheorems ← ds.foldrM (fun n a => a.addDeclToUnfold n) {}
      let simpTheorems ← ts.foldrM (fun n a => a.addConst n) simpTheorems
      let ctx ← Meta.Simp.mkContext {} #[simpTheorems]
      let simpProcs ← ps.foldrM (fun n a => a.add n false) {}
      let (some mv, _) ← Meta.simpTarget mv ctx simpProcs | throwError "simp failed"
      mv.refl
      addThm q($x + $y = $z) q(Eq.trans (BitVec.add_eq_adc' $x $y) $h)
    | _ => return none
  | _ => return none

end Smt.Reconstruct.BitVec
