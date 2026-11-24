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
  | .INTERNAL_KIND =>
    -- Instances of RARE rules contain symbolic constants `(@bv n w)` of value `n` and width `w`,
    -- which cvc5 evaluates in separate steps. Their kind is internal to cvc5, so they are
    -- recognized by name.
    unless t.toString.startsWith "(@bv " do return none
    let w : Nat := t.getSort!.getBitVectorSize!.toNat
    if t[0]!.getKind! == .CONST_INTEGER && t[0]!.getIntegerValue! ≥ 0 then
      let n : Nat := t[0]!.getIntegerValue!.toNat
      return q(BitVec.ofNat $w $n)
    let n : Q(Int) ← reconstructTerm t[0]!
    return q(BitVec.ofInt $w $n)
  | _ => return none
where
  leftAssocOp (op : Expr) (t : cvc5.Term) : ReconstructM Expr := do
    let mut curr ← reconstructTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op curr (← reconstructTerm t[i]!)
    return curr

/-! ### RARE rewrites

Each rewrite rule `bv-foo-bar` is proved by the theorem `Rewrite.foo_bar`. The arguments of a
`DSL_REWRITE` step are the rule's identifier followed by its parameters in declaration order. The
theorems take only the parameters that are not determined by the others; e.g., `bv-extract-extract`
has parameters `ll` and `kk` for the numerals `i + l` and `i + k`, which SMT-LIB needs as indices of
`extract`. The hypotheses of the theorems are closed propositions about numerals, which are proved
by evaluation. -/

/-- Reconstruct a list of bit-vectors of possibly different widths. -/
def reconstructHBitVecList (ts : Array cvc5.Term) : ReconstructM Q(HBitVecList) :=
  ts.foldrM (init := q(HBitVecList.nil)) fun t xs => do
    let w : Nat := t.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm t
    return q($x ::ₕ $xs)

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
/-- Prove the hypotheses of the instance `h` of a rewrite theorem by evaluation. -/
def proveHypotheses? (h : Expr) : MetaM (Option Expr) := do
  let mut h := h
  repeat
    let .forallE _ p _ _ ← inferType h | break
    let some hp ← proveSideCondition? p | return none
    h := mkApp h hp
  return some h

/-- The theorem proving the rewrite rule `rule`, applied to the arguments `args` of a `DSL_REWRITE`
step but not yet to proofs of its hypotheses. -/
def rewriteTheorem? (rule : cvc5.ProofRewriteRule) (args : Array cvc5.Term) :
    ReconstructM (Option Expr) := do
  match rule with
  | .BV_CONCAT_EXTRACT_MERGE =>
    let w : Nat := args[2]!.getSort!.getBitVectorSize!.toNat
    let xs : Q(HBitVecList) ← reconstructHBitVecList args[1]!.getChildren
    let s : Q(BitVec $w) ← reconstructTerm args[2]!
    let ys : Q(HBitVecList) ← reconstructHBitVecList args[3]!.getChildren
    let i : Nat := args[4]!.getIntegerValue!.toNat
    let j : Nat := args[5]!.getIntegerValue!.toNat
    let k : Nat := args[7]!.getIntegerValue!.toNat
    return q(@Rewrite.concat_extract_merge $w $xs $s $ys $i $j $k)
  | .BV_EXTRACT_EXTRACT =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let i : Nat := args[2]!.getIntegerValue!.toNat
    let j : Nat := args[3]!.getIntegerValue!.toNat
    let k : Nat := args[4]!.getIntegerValue!.toNat
    let l : Nat := args[5]!.getIntegerValue!.toNat
    return q(@Rewrite.extract_extract $w $x $i $j $k $l)
  | .BV_EXTRACT_WHOLE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.extract_whole $w $x)
  | .BV_EXTRACT_CONCAT_1 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let v : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let xs : Q(HBitVecList) ← reconstructHBitVecList args[2]!.getChildren
    let y : Q(BitVec $v) ← reconstructTerm args[3]!
    let i : Nat := args[4]!.getIntegerValue!.toNat
    let j : Nat := args[5]!.getIntegerValue!.toNat
    return q(@Rewrite.extract_concat_1 $w $v $x $xs $y $i $j)
  | .BV_EXTRACT_CONCAT_2 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let v : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let xs : Q(HBitVecList) ← reconstructHBitVecList args[2]!.getChildren
    let y : Q(BitVec $v) ← reconstructTerm args[3]!
    let i : Nat := args[4]!.getIntegerValue!.toNat
    let j : Nat := args[5]!.getIntegerValue!.toNat
    return q(@Rewrite.extract_concat_2 $w $v $x $xs $y $i $j)
  | .BV_EXTRACT_CONCAT_3 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let v : Nat := args[2]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $v) ← reconstructTerm args[2]!
    let xs : Q(HBitVecList) ← reconstructHBitVecList args[3]!.getChildren
    let i : Nat := args[4]!.getIntegerValue!.toNat
    let j : Nat := args[5]!.getIntegerValue!.toNat
    return q(@Rewrite.extract_concat_3 $w $v $x $y $xs $i $j)
  | .BV_EXTRACT_CONCAT_4 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let v : Nat := args[2]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $v) ← reconstructTerm args[2]!
    let xs : Q(HBitVecList) ← reconstructHBitVecList args[3]!.getChildren
    let i : Nat := args[4]!.getIntegerValue!.toNat
    let j : Nat := args[5]!.getIntegerValue!.toNat
    return q(@Rewrite.extract_concat_4 $w $v $x $y $xs $i $j)
  | .BV_EQ_EXTRACT_ELIM1 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let i : Nat := args[3]!.getIntegerValue!.toNat
    let j : Nat := args[4]!.getIntegerValue!.toNat
    let y : Q(BitVec ($j - $i + 1)) ← reconstructTerm args[2]!
    return q(@Rewrite.eq_extract_elim1 $w $x $i $j $y)
  | .BV_EQ_EXTRACT_ELIM2 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let j : Nat := args[3]!.getIntegerValue!.toNat
    let y : Q(BitVec ($j - 0 + 1)) ← reconstructTerm args[2]!
    return q(@Rewrite.eq_extract_elim2 $w $x $j $y)
  | .BV_EQ_EXTRACT_ELIM3 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let i : Nat := args[3]!.getIntegerValue!.toNat
    let y : Q(BitVec ($w - 1 - $i + 1)) ← reconstructTerm args[2]!
    return q(@Rewrite.eq_extract_elim3 $w $x $i $y)
  | .BV_EXTRACT_NOT =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let i : Nat := args[2]!.getIntegerValue!.toNat
    let j : Nat := args[3]!.getIntegerValue!.toNat
    return q(@Rewrite.extract_not $w $x $i $j)
  | .BV_EXTRACT_SIGN_EXTEND_1 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let low : Nat := args[2]!.getIntegerValue!.toNat
    let high : Nat := args[3]!.getIntegerValue!.toNat
    let k : Nat := args[4]!.getIntegerValue!.toNat
    return q(@Rewrite.extract_sign_extend_1 $w $x $low $high $k)
  | .BV_EXTRACT_SIGN_EXTEND_2 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let low : Nat := args[2]!.getIntegerValue!.toNat
    let high : Nat := args[3]!.getIntegerValue!.toNat
    let k : Nat := args[4]!.getIntegerValue!.toNat
    return q(@Rewrite.extract_sign_extend_2 $w $x $low $high $k)
  | .BV_EXTRACT_SIGN_EXTEND_3 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let low : Nat := args[2]!.getIntegerValue!.toNat
    let high : Nat := args[3]!.getIntegerValue!.toNat
    let k : Nat := args[4]!.getIntegerValue!.toNat
    return q(@Rewrite.extract_sign_extend_3 $w $x $low $high $k)
  | .BV_NOT_XOR =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x1 : Q(BitVec $w) ← reconstructTerm args[1]!
    let x2 : Q(BitVec $w) ← reconstructTerm args[2]!
    let xs : Q(List (BitVec $w)) ← reconstructTerms args[3]!.getChildren
    return q(@Rewrite.not_xor $w $x1 $x2 $xs)
  | .BV_AND_SIMPLIFY_1 =>
    let w : Nat := args[5]!.getIntegerValue!.toNat
    let xs : Q(List (BitVec $w)) ← reconstructTerms args[1]!.getChildren
    let ys : Q(List (BitVec $w)) ← reconstructTerms args[2]!.getChildren
    let zs : Q(List (BitVec $w)) ← reconstructTerms args[3]!.getChildren
    let x : Q(BitVec $w) ← reconstructTerm args[4]!
    return q(@Rewrite.and_simplify_1 $w $xs $ys $zs $x)
  | .BV_AND_SIMPLIFY_2 =>
    let w : Nat := args[5]!.getIntegerValue!.toNat
    let xs : Q(List (BitVec $w)) ← reconstructTerms args[1]!.getChildren
    let ys : Q(List (BitVec $w)) ← reconstructTerms args[2]!.getChildren
    let zs : Q(List (BitVec $w)) ← reconstructTerms args[3]!.getChildren
    let x : Q(BitVec $w) ← reconstructTerm args[4]!
    return q(@Rewrite.and_simplify_2 $w $xs $ys $zs $x)
  | .BV_OR_SIMPLIFY_1 =>
    let w : Nat := args[5]!.getIntegerValue!.toNat
    let xs : Q(List (BitVec $w)) ← reconstructTerms args[1]!.getChildren
    let ys : Q(List (BitVec $w)) ← reconstructTerms args[2]!.getChildren
    let zs : Q(List (BitVec $w)) ← reconstructTerms args[3]!.getChildren
    let x : Q(BitVec $w) ← reconstructTerm args[4]!
    return q(@Rewrite.or_simplify_1 $w $xs $ys $zs $x)
  | .BV_OR_SIMPLIFY_2 =>
    let w : Nat := args[5]!.getIntegerValue!.toNat
    let xs : Q(List (BitVec $w)) ← reconstructTerms args[1]!.getChildren
    let ys : Q(List (BitVec $w)) ← reconstructTerms args[2]!.getChildren
    let zs : Q(List (BitVec $w)) ← reconstructTerms args[3]!.getChildren
    let x : Q(BitVec $w) ← reconstructTerm args[4]!
    return q(@Rewrite.or_simplify_2 $w $xs $ys $zs $x)
  | .BV_XOR_SIMPLIFY_1 =>
    let w : Nat := args[4]!.getSort!.getBitVectorSize!.toNat
    let xs : Q(List (BitVec $w)) ← reconstructTerms args[1]!.getChildren
    let ys : Q(List (BitVec $w)) ← reconstructTerms args[2]!.getChildren
    let zs : Q(List (BitVec $w)) ← reconstructTerms args[3]!.getChildren
    let x : Q(BitVec $w) ← reconstructTerm args[4]!
    return q(@Rewrite.xor_simplify_1 $w $xs $ys $zs $x)
  | .BV_XOR_SIMPLIFY_2 =>
    let w : Nat := args[4]!.getSort!.getBitVectorSize!.toNat
    let xs : Q(List (BitVec $w)) ← reconstructTerms args[1]!.getChildren
    let ys : Q(List (BitVec $w)) ← reconstructTerms args[2]!.getChildren
    let zs : Q(List (BitVec $w)) ← reconstructTerms args[3]!.getChildren
    let x : Q(BitVec $w) ← reconstructTerm args[4]!
    return q(@Rewrite.xor_simplify_2 $w $xs $ys $zs $x)
  | .BV_XOR_SIMPLIFY_3 =>
    let w : Nat := args[4]!.getSort!.getBitVectorSize!.toNat
    let xs : Q(List (BitVec $w)) ← reconstructTerms args[1]!.getChildren
    let ys : Q(List (BitVec $w)) ← reconstructTerms args[2]!.getChildren
    let zs : Q(List (BitVec $w)) ← reconstructTerms args[3]!.getChildren
    let x : Q(BitVec $w) ← reconstructTerm args[4]!
    return q(@Rewrite.xor_simplify_3 $w $xs $ys $zs $x)
  | .BV_ULT_ADD_ONE =>
    let w : Nat := args[5]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let ys : Q(List (BitVec $w)) ← reconstructTerms args[2]!.getChildren
    let zs : Q(List (BitVec $w)) ← reconstructTerms args[3]!.getChildren
    return q(@Rewrite.ult_add_one $w $x $ys $zs)
  | .BV_MULT_SLT_MULT_1 =>
    let tn : Nat := args[6]!.getIntegerValue!.toNat
    let an : Nat := args[7]!.getIntegerValue!.toNat
    let x : Q(BitVec $tn) ← reconstructTerm args[1]!
    let y : Q(BitVec $tn) ← reconstructTerm args[2]!
    let a : Q(BitVec $an) ← reconstructTerm args[3]!
    let n : Nat := args[4]!.getIntegerValue!.toNat
    let m : Nat := args[5]!.getIntegerValue!.toNat
    return q(@Rewrite.mult_slt_mult_1 $tn $an $x $y $a $n $m)
  | .BV_MULT_SLT_MULT_2 =>
    let tn : Nat := args[6]!.getIntegerValue!.toNat
    let an : Nat := args[7]!.getIntegerValue!.toNat
    let x : Q(BitVec $tn) ← reconstructTerm args[1]!
    let y : Q(BitVec $tn) ← reconstructTerm args[2]!
    let a : Q(BitVec $an) ← reconstructTerm args[3]!
    let n : Nat := args[4]!.getIntegerValue!.toNat
    let m : Nat := args[5]!.getIntegerValue!.toNat
    return q(@Rewrite.mult_slt_mult_2 $tn $an $x $y $a $n $m)
  | .BV_COMMUTATIVE_XOR =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.commutative_xor $w $x $y)
  | .BV_COMMUTATIVE_COMP =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.commutative_comp $w $x $y)
  | .BV_ZERO_EXTEND_ELIMINATE_0 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.zero_extend_eliminate_0 $w $x)
  | .BV_SIGN_EXTEND_ELIMINATE_0 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.sign_extend_eliminate_0 $w $x)
  | .BV_NOT_NEQ =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.not_neq $w $x)
  | .BV_ULT_ONES =>
    let w : Nat := args[3]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.ult_ones $w $x)
  | .BV_CONCAT_MERGE_CONST =>
    let xs : Q(HBitVecList) ← reconstructHBitVecList args[1]!.getChildren
    let n1 : Nat := args[2]!.getIntegerValue!.toNat
    let w1 : Nat := args[3]!.getIntegerValue!.toNat
    let n2 : Nat := args[4]!.getIntegerValue!.toNat
    let w2 : Nat := args[5]!.getIntegerValue!.toNat
    let zs : Q(HBitVecList) ← reconstructHBitVecList args[7]!.getChildren
    return q(@Rewrite.concat_merge_const $xs $n1 $w1 $n2 $w2 $zs)
  | .BV_COMMUTATIVE_ADD =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.commutative_add $w $x $y)
  | .BV_SUB_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.sub_eliminate $w $x $y)
  | .BV_ITE_WIDTH_ONE =>
    let x : Q(BitVec 1) ← reconstructTerm args[1]!
    return q(@Rewrite.ite_width_one $x)
  | .BV_ITE_WIDTH_ONE_NOT =>
    let x : Q(BitVec 1) ← reconstructTerm args[1]!
    return q(@Rewrite.ite_width_one_not $x)
  | .BV_EQ_XOR_SOLVE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    let z : Q(BitVec $w) ← reconstructTerm args[3]!
    return q(@Rewrite.eq_xor_solve $w $x $y $z)
  | .BV_EQ_NOT_SOLVE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.eq_not_solve $w $x $y)
  | .BV_UGT_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.ugt_eliminate $w $x $y)
  | .BV_UGE_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.uge_eliminate $w $x $y)
  | .BV_SGT_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.sgt_eliminate $w $x $y)
  | .BV_SGE_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.sge_eliminate $w $x $y)
  | .BV_SLE_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.sle_eliminate $w $x $y)
  | .BV_REDOR_ELIMINATE =>
    let w : Nat := args[2]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.redor_eliminate $w $x)
  | .BV_REDAND_ELIMINATE =>
    let w : Nat := args[2]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.redand_eliminate $w $x)
  | .BV_ULE_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.ule_eliminate $w $x $y)
  | .BV_COMP_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.comp_eliminate $w $x $y)
  | .BV_ROTATE_LEFT_ELIMINATE_1 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let amount : Nat := args[2]!.getIntegerValue!.toNat
    return q(@Rewrite.rotate_left_eliminate_1 $w $x $amount)
  | .BV_ROTATE_LEFT_ELIMINATE_2 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let amount : Nat := args[2]!.getIntegerValue!.toNat
    return q(@Rewrite.rotate_left_eliminate_2 $w $x $amount)
  | .BV_ROTATE_RIGHT_ELIMINATE_1 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let amount : Nat := args[2]!.getIntegerValue!.toNat
    return q(@Rewrite.rotate_right_eliminate_1 $w $x $amount)
  | .BV_ROTATE_RIGHT_ELIMINATE_2 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let amount : Nat := args[2]!.getIntegerValue!.toNat
    return q(@Rewrite.rotate_right_eliminate_2 $w $x $amount)
  | .BV_NAND_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.nand_eliminate $w $x $y)
  | .BV_NOR_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.nor_eliminate $w $x $y)
  | .BV_XNOR_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.xnor_eliminate $w $x $y)
  | .BV_SDIV_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.sdiv_eliminate $w $x $y)
  | .BV_ZERO_EXTEND_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let n : Nat := args[2]!.getIntegerValue!.toNat
    return q(@Rewrite.zero_extend_eliminate $w $x $n)
  | .BV_UADDO_ELIMINATE =>
    let w : Nat := args[3]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.uaddo_eliminate $w $x $y)
  | .BV_SADDO_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.saddo_eliminate $w $x $y)
  | .BV_SDIVO_ELIMINATE =>
    let w : Nat := args[3]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.sdivo_eliminate $w $x $y)
  | .BV_SMOD_ELIMINATE =>
    let w : Nat := args[3]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.smod_eliminate $w $x $y)
  | .BV_SREM_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.srem_eliminate $w $x $y)
  | .BV_USUBO_ELIMINATE =>
    let n : Nat := args[3]!.getIntegerValue!.toNat
    let x : Q(BitVec $n) ← reconstructTerm args[1]!
    let y : Q(BitVec $n) ← reconstructTerm args[2]!
    return q(@Rewrite.usubo_eliminate $n $x $y)
  | .BV_SSUBO_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.ssubo_eliminate $w $x $y)
  | .BV_NEGO_ELIMINATE =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.nego_eliminate $w $x)
  | .BV_ITE_EQUAL_CHILDREN =>
    let w : Nat := args[2]!.getSort!.getBitVectorSize!.toNat
    let c : Q(BitVec 1) ← reconstructTerm args[1]!
    let x : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.ite_equal_children $w $c $x)
  | .BV_ITE_CONST_CHILDREN_1 =>
    let c : Q(BitVec 1) ← reconstructTerm args[1]!
    return q(@Rewrite.ite_const_children_1 $c)
  | .BV_ITE_CONST_CHILDREN_2 =>
    let c : Q(BitVec 1) ← reconstructTerm args[1]!
    return q(@Rewrite.ite_const_children_2 $c)
  | .BV_ITE_EQUAL_COND_1 =>
    let w : Nat := args[2]!.getSort!.getBitVectorSize!.toNat
    let c0 : Q(BitVec 1) ← reconstructTerm args[1]!
    let t0 : Q(BitVec $w) ← reconstructTerm args[2]!
    let e0 : Q(BitVec $w) ← reconstructTerm args[3]!
    let e1 : Q(BitVec $w) ← reconstructTerm args[4]!
    return q(@Rewrite.ite_equal_cond_1 $w $c0 $t0 $e0 $e1)
  | .BV_ITE_EQUAL_COND_2 =>
    let w : Nat := args[2]!.getSort!.getBitVectorSize!.toNat
    let c0 : Q(BitVec 1) ← reconstructTerm args[1]!
    let t0 : Q(BitVec $w) ← reconstructTerm args[2]!
    let t1 : Q(BitVec $w) ← reconstructTerm args[3]!
    let e1 : Q(BitVec $w) ← reconstructTerm args[4]!
    return q(@Rewrite.ite_equal_cond_2 $w $c0 $t0 $t1 $e1)
  | .BV_ITE_EQUAL_COND_3 =>
    let w : Nat := args[2]!.getSort!.getBitVectorSize!.toNat
    let c0 : Q(BitVec 1) ← reconstructTerm args[1]!
    let t0 : Q(BitVec $w) ← reconstructTerm args[2]!
    let e0 : Q(BitVec $w) ← reconstructTerm args[3]!
    let t1 : Q(BitVec $w) ← reconstructTerm args[4]!
    let e1 : Q(BitVec $w) ← reconstructTerm args[5]!
    return q(@Rewrite.ite_equal_cond_3 $w $c0 $t0 $e0 $t1 $e1)
  | .BV_ITE_MERGE_THEN_IF =>
    let w : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let c0 : Q(BitVec 1) ← reconstructTerm args[1]!
    let c1 : Q(BitVec 1) ← reconstructTerm args[2]!
    let t1 : Q(BitVec $w) ← reconstructTerm args[3]!
    let e1 : Q(BitVec $w) ← reconstructTerm args[4]!
    return q(@Rewrite.ite_merge_then_if $w $c0 $c1 $t1 $e1)
  | .BV_ITE_MERGE_ELSE_IF =>
    let w : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let c0 : Q(BitVec 1) ← reconstructTerm args[1]!
    let c1 : Q(BitVec 1) ← reconstructTerm args[2]!
    let t1 : Q(BitVec $w) ← reconstructTerm args[3]!
    let e1 : Q(BitVec $w) ← reconstructTerm args[4]!
    return q(@Rewrite.ite_merge_else_if $w $c0 $c1 $t1 $e1)
  | .BV_ITE_MERGE_THEN_ELSE =>
    let w : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let c0 : Q(BitVec 1) ← reconstructTerm args[1]!
    let c1 : Q(BitVec 1) ← reconstructTerm args[2]!
    let t0 : Q(BitVec $w) ← reconstructTerm args[3]!
    let e1 : Q(BitVec $w) ← reconstructTerm args[4]!
    return q(@Rewrite.ite_merge_then_else $w $c0 $c1 $t0 $e1)
  | .BV_ITE_MERGE_ELSE_ELSE =>
    let w : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let c0 : Q(BitVec 1) ← reconstructTerm args[1]!
    let c1 : Q(BitVec 1) ← reconstructTerm args[2]!
    let t1 : Q(BitVec $w) ← reconstructTerm args[3]!
    let t0 : Q(BitVec $w) ← reconstructTerm args[4]!
    return q(@Rewrite.ite_merge_else_else $w $c0 $c1 $t1 $t0)
  | .BV_SHL_BY_CONST_0 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.shl_by_const_0 $w $x)
  | .BV_SHL_BY_CONST_1 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let amount : Nat := args[2]!.getIntegerValue!.toNat
    return q(@Rewrite.shl_by_const_1 $w $x $amount)
  | .BV_SHL_BY_CONST_2 =>
    let w : Nat := args[4]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let amount : Nat := args[2]!.getIntegerValue!.toNat
    return q(@Rewrite.shl_by_const_2 $w $x $amount)
  | .BV_LSHR_BY_CONST_0 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.lshr_by_const_0 $w $x)
  | .BV_LSHR_BY_CONST_1 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let amount : Nat := args[2]!.getIntegerValue!.toNat
    return q(@Rewrite.lshr_by_const_1 $w $x $amount)
  | .BV_LSHR_BY_CONST_2 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let amount : Nat := args[2]!.getIntegerValue!.toNat
    return q(@Rewrite.lshr_by_const_2 $w $x $amount)
  | .BV_ASHR_BY_CONST_0 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.ashr_by_const_0 $w $x)
  | .BV_ASHR_BY_CONST_1 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let amount : Nat := args[2]!.getIntegerValue!.toNat
    return q(@Rewrite.ashr_by_const_1 $w $x $amount)
  | .BV_ASHR_BY_CONST_2 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let amount : Nat := args[2]!.getIntegerValue!.toNat
    return q(@Rewrite.ashr_by_const_2 $w $x $amount)
  | .BV_AND_CONCAT_PULLUP =>
    let wy : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let wz : Nat := args[4]!.getSort!.getBitVectorSize!.toNat
    let y : Q(BitVec $wy) ← reconstructTerm args[3]!
    let z : Q(BitVec $wz) ← reconstructTerm args[4]!
    let ys : Q(HBitVecList) ← reconstructHBitVecList args[5]!.getChildren
    let xs : Q(List (BitVec ($ys ++ $z ::ₕ $y ::ₕ .nil).width)) ←
      reconstructTerms args[1]!.getChildren
    let ws : Q(List (BitVec ($ys ++ $z ::ₕ $y ::ₕ .nil).width)) ←
      reconstructTerms args[2]!.getChildren
    return q(@Rewrite.and_concat_pullup $wy $wz $y $z $ys $xs $ws)
  | .BV_OR_CONCAT_PULLUP =>
    let wy : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let wz : Nat := args[4]!.getSort!.getBitVectorSize!.toNat
    let y : Q(BitVec $wy) ← reconstructTerm args[3]!
    let z : Q(BitVec $wz) ← reconstructTerm args[4]!
    let ys : Q(HBitVecList) ← reconstructHBitVecList args[5]!.getChildren
    let xs : Q(List (BitVec ($ys ++ $z ::ₕ $y ::ₕ .nil).width)) ←
      reconstructTerms args[1]!.getChildren
    let ws : Q(List (BitVec ($ys ++ $z ::ₕ $y ::ₕ .nil).width)) ←
      reconstructTerms args[2]!.getChildren
    return q(@Rewrite.or_concat_pullup $wy $wz $y $z $ys $xs $ws)
  | .BV_XOR_CONCAT_PULLUP =>
    let wy : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let wz : Nat := args[4]!.getSort!.getBitVectorSize!.toNat
    let y : Q(BitVec $wy) ← reconstructTerm args[3]!
    let z : Q(BitVec $wz) ← reconstructTerm args[4]!
    let ys : Q(HBitVecList) ← reconstructHBitVecList args[5]!.getChildren
    let xs : Q(List (BitVec ($ys ++ $z ::ₕ $y ::ₕ .nil).width)) ←
      reconstructTerms args[1]!.getChildren
    let ws : Q(List (BitVec ($ys ++ $z ::ₕ $y ::ₕ .nil).width)) ←
      reconstructTerms args[2]!.getChildren
    return q(@Rewrite.xor_concat_pullup $wy $wz $y $z $ys $xs $ws)
  | .BV_AND_CONCAT_PULLUP2 =>
    let wy : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let wz : Nat := args[4]!.getSort!.getBitVectorSize!.toNat
    let y : Q(BitVec $wy) ← reconstructTerm args[3]!
    let z : Q(BitVec $wz) ← reconstructTerm args[4]!
    let ys : Q(HBitVecList) ← reconstructHBitVecList args[5]!.getChildren
    let xs : Q(List (BitVec ($z ::ₕ $y ::ₕ $ys).width)) ← reconstructTerms args[1]!.getChildren
    let ws : Q(List (BitVec ($z ::ₕ $y ::ₕ $ys).width)) ← reconstructTerms args[2]!.getChildren
    return q(@Rewrite.and_concat_pullup2 $wy $wz $y $z $ys $xs $ws)
  | .BV_OR_CONCAT_PULLUP2 =>
    let wy : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let wz : Nat := args[4]!.getSort!.getBitVectorSize!.toNat
    let y : Q(BitVec $wy) ← reconstructTerm args[3]!
    let z : Q(BitVec $wz) ← reconstructTerm args[4]!
    let ys : Q(HBitVecList) ← reconstructHBitVecList args[5]!.getChildren
    let xs : Q(List (BitVec ($z ::ₕ $y ::ₕ $ys).width)) ← reconstructTerms args[1]!.getChildren
    let ws : Q(List (BitVec ($z ::ₕ $y ::ₕ $ys).width)) ← reconstructTerms args[2]!.getChildren
    return q(@Rewrite.or_concat_pullup2 $wy $wz $y $z $ys $xs $ws)
  | .BV_XOR_CONCAT_PULLUP2 =>
    let wy : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let wz : Nat := args[4]!.getSort!.getBitVectorSize!.toNat
    let y : Q(BitVec $wy) ← reconstructTerm args[3]!
    let z : Q(BitVec $wz) ← reconstructTerm args[4]!
    let ys : Q(HBitVecList) ← reconstructHBitVecList args[5]!.getChildren
    let xs : Q(List (BitVec ($z ::ₕ $y ::ₕ $ys).width)) ← reconstructTerms args[1]!.getChildren
    let ws : Q(List (BitVec ($z ::ₕ $y ::ₕ $ys).width)) ← reconstructTerms args[2]!.getChildren
    return q(@Rewrite.xor_concat_pullup2 $wy $wz $y $z $ys $xs $ws)
  | .BV_AND_CONCAT_PULLUP3 =>
    let wy : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let wz : Nat := args[4]!.getSort!.getBitVectorSize!.toNat
    let wu : Nat := args[5]!.getSort!.getBitVectorSize!.toNat
    let xs : Q(List (BitVec ($wz + $wy + $wu))) ← reconstructTerms args[1]!.getChildren
    let ws : Q(List (BitVec ($wz + $wy + $wu))) ← reconstructTerms args[2]!.getChildren
    let y : Q(BitVec $wy) ← reconstructTerm args[3]!
    let z : Q(BitVec $wz) ← reconstructTerm args[4]!
    let u : Q(BitVec $wu) ← reconstructTerm args[5]!
    return q(@Rewrite.and_concat_pullup3 $wy $wz $wu $xs $ws $y $z $u)
  | .BV_OR_CONCAT_PULLUP3 =>
    let wy : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let wz : Nat := args[4]!.getSort!.getBitVectorSize!.toNat
    let wu : Nat := args[5]!.getSort!.getBitVectorSize!.toNat
    let xs : Q(List (BitVec ($wz + $wy + $wu))) ← reconstructTerms args[1]!.getChildren
    let ws : Q(List (BitVec ($wz + $wy + $wu))) ← reconstructTerms args[2]!.getChildren
    let y : Q(BitVec $wy) ← reconstructTerm args[3]!
    let z : Q(BitVec $wz) ← reconstructTerm args[4]!
    let u : Q(BitVec $wu) ← reconstructTerm args[5]!
    return q(@Rewrite.or_concat_pullup3 $wy $wz $wu $xs $ws $y $z $u)
  | .BV_XOR_CONCAT_PULLUP3 =>
    let wy : Nat := args[3]!.getSort!.getBitVectorSize!.toNat
    let wz : Nat := args[4]!.getSort!.getBitVectorSize!.toNat
    let wu : Nat := args[5]!.getSort!.getBitVectorSize!.toNat
    let xs : Q(List (BitVec ($wz + $wy + $wu))) ← reconstructTerms args[1]!.getChildren
    let ws : Q(List (BitVec ($wz + $wy + $wu))) ← reconstructTerms args[2]!.getChildren
    let y : Q(BitVec $wy) ← reconstructTerm args[3]!
    let z : Q(BitVec $wz) ← reconstructTerm args[4]!
    let u : Q(BitVec $wu) ← reconstructTerm args[5]!
    return q(@Rewrite.xor_concat_pullup3 $wy $wz $wu $xs $ws $y $z $u)
  | .BV_XOR_DUPLICATE =>
    let w : Nat := args[2]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.xor_duplicate $w $x)
  | .BV_XOR_ONES =>
    let w : Nat := args[4]!.getIntegerValue!.toNat
    let xs : Q(List (BitVec $w)) ← reconstructTerms args[1]!.getChildren
    let zs : Q(List (BitVec $w)) ← reconstructTerms args[2]!.getChildren
    return q(@Rewrite.xor_ones $w $xs $zs)
  | .BV_XOR_NOT =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.xor_not $w $x $y)
  | .BV_NOT_IDEMP =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.not_idemp $w $x)
  | .BV_ULT_ZERO_1 =>
    let n : Nat := args[2]!.getIntegerValue!.toNat
    let x : Q(BitVec $n) ← reconstructTerm args[1]!
    return q(@Rewrite.ult_zero_1 $n $x)
  | .BV_ULT_ZERO_2 =>
    let n : Nat := args[2]!.getIntegerValue!.toNat
    let x : Q(BitVec $n) ← reconstructTerm args[1]!
    return q(@Rewrite.ult_zero_2 $n $x)
  | .BV_ULT_SELF =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.ult_self $w $x)
  | .BV_LT_SELF =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.lt_self $w $x)
  | .BV_ULE_SELF =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.ule_self $w $x)
  | .BV_ULE_ZERO =>
    let n : Nat := args[2]!.getIntegerValue!.toNat
    let x : Q(BitVec $n) ← reconstructTerm args[1]!
    return q(@Rewrite.ule_zero $n $x)
  | .BV_ZERO_ULE =>
    let n : Nat := args[2]!.getIntegerValue!.toNat
    let x : Q(BitVec $n) ← reconstructTerm args[1]!
    return q(@Rewrite.zero_ule $n $x)
  | .BV_SLE_SELF =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.sle_self $w $x)
  | .BV_ULE_MAX =>
    let w : Nat := args[3]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.ule_max $w $x)
  | .BV_NOT_ULT =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let y : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.not_ult $w $x $y)
  | .BV_MULT_POW2_1 =>
    let size : Nat := args[4]!.getIntegerValue!.toNat
    let xs : Q(List (BitVec $size)) ← reconstructTerms args[1]!.getChildren
    let ys : Q(List (BitVec $size)) ← reconstructTerms args[2]!.getChildren
    let z : Q(BitVec $size) ← reconstructTerm args[3]!
    let n : Nat := args[5]!.getIntegerValue!.toNat
    let exponent : Nat := args[6]!.getIntegerValue!.toNat
    let u : Nat := args[7]!.getIntegerValue!.toNat
    return q(@Rewrite.mult_pow2_1 $size $xs $ys $z $n $exponent $u)
  | .BV_MULT_POW2_2 =>
    let size : Nat := args[4]!.getIntegerValue!.toNat
    let xs : Q(List (BitVec $size)) ← reconstructTerms args[1]!.getChildren
    let ys : Q(List (BitVec $size)) ← reconstructTerms args[2]!.getChildren
    let z : Q(BitVec $size) ← reconstructTerm args[3]!
    let n : Nat := args[5]!.getIntegerValue!.toNat
    let exponent : Nat := args[6]!.getIntegerValue!.toNat
    let u : Nat := args[7]!.getIntegerValue!.toNat
    return q(@Rewrite.mult_pow2_2 $size $xs $ys $z $n $exponent $u)
  | .BV_MULT_POW2_2B =>
    let size : Nat := args[2]!.getIntegerValue!.toNat
    let z : Q(BitVec $size) ← reconstructTerm args[1]!
    let n : Nat := args[3]!.getIntegerValue!.toNat
    let exponent : Nat := args[4]!.getIntegerValue!.toNat
    let u : Nat := args[5]!.getIntegerValue!.toNat
    return q(@Rewrite.mult_pow2_2b $size $z $n $exponent $u)
  | .BV_EXTRACT_MULT_LEADING_BIT =>
    let wx : Nat := args[5]!.getSort!.getBitVectorSize!.toNat
    let wy : Nat := args[8]!.getSort!.getBitVectorSize!.toNat
    let high : Nat := args[1]!.getIntegerValue!.toNat
    let low : Nat := args[2]!.getIntegerValue!.toNat
    let x1i : Nat := args[3]!.getIntegerValue!.toNat
    let x1in : Nat := args[4]!.getIntegerValue!.toNat
    let x2 : Q(BitVec $wx) ← reconstructTerm args[5]!
    let y1i : Nat := args[6]!.getIntegerValue!.toNat
    let y1in : Nat := args[7]!.getIntegerValue!.toNat
    let y2 : Q(BitVec $wy) ← reconstructTerm args[8]!
    return q(@Rewrite.extract_mult_leading_bit $wx $wy $high $low $x1i $x1in $x2 $y1i $y1in $y2)
  | .BV_UDIV_POW2_NOT_ONE =>
    let n : Nat := args[3]!.getIntegerValue!.toNat
    let x : Q(BitVec $n) ← reconstructTerm args[1]!
    let v : Nat := args[2]!.getIntegerValue!.toNat
    let power : Nat := args[4]!.getIntegerValue!.toNat
    return q(@Rewrite.udiv_pow2_not_one $n $x $v $power)
  | .BV_UDIV_ZERO =>
    let n : Nat := args[2]!.getIntegerValue!.toNat
    let x : Q(BitVec $n) ← reconstructTerm args[1]!
    return q(@Rewrite.udiv_zero $n $x)
  | .BV_UDIV_ONE =>
    let n : Nat := args[2]!.getIntegerValue!.toNat
    let x : Q(BitVec $n) ← reconstructTerm args[1]!
    return q(@Rewrite.udiv_one $n $x)
  | .BV_UREM_POW2_NOT_ONE =>
    let n : Nat := args[3]!.getIntegerValue!.toNat
    let x : Q(BitVec $n) ← reconstructTerm args[1]!
    let v : Nat := args[2]!.getIntegerValue!.toNat
    let nmp : Nat := args[4]!.getIntegerValue!.toNat
    let pm1 : Nat := args[5]!.getIntegerValue!.toNat
    return q(@Rewrite.urem_pow2_not_one $n $x $v $nmp $pm1)
  | .BV_UREM_ONE =>
    let n : Nat := args[2]!.getIntegerValue!.toNat
    let x : Q(BitVec $n) ← reconstructTerm args[1]!
    return q(@Rewrite.urem_one $n $x)
  | .BV_UREM_SELF =>
    let w : Nat := args[2]!.getIntegerValue!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    return q(@Rewrite.urem_self $w $x)
  | .BV_SHL_ZERO =>
    let n : Nat := args[2]!.getIntegerValue!.toNat
    let a : Q(BitVec $n) ← reconstructTerm args[1]!
    return q(@Rewrite.shl_zero $n $a)
  | .BV_LSHR_ZERO =>
    let n : Nat := args[2]!.getIntegerValue!.toNat
    let a : Q(BitVec $n) ← reconstructTerm args[1]!
    return q(@Rewrite.lshr_zero $n $a)
  | .BV_ASHR_ZERO =>
    let n : Nat := args[2]!.getIntegerValue!.toNat
    let a : Q(BitVec $n) ← reconstructTerm args[1]!
    return q(@Rewrite.ashr_zero $n $a)
  | .BV_UGT_UREM =>
    let w : Nat := args[3]!.getIntegerValue!.toNat
    let y : Q(BitVec $w) ← reconstructTerm args[1]!
    let x : Q(BitVec $w) ← reconstructTerm args[2]!
    return q(@Rewrite.ugt_urem $w $y $x)
  | .BV_ULT_ONE =>
    let n : Nat := args[2]!.getIntegerValue!.toNat
    let x : Q(BitVec $n) ← reconstructTerm args[1]!
    return q(@Rewrite.ult_one $n $x)
  | .BV_MERGE_SIGN_EXTEND_1 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let i : Nat := args[2]!.getIntegerValue!.toNat
    let j : Nat := args[3]!.getIntegerValue!.toNat
    return q(@Rewrite.merge_sign_extend_1 $w $x $i $j)
  | .BV_MERGE_SIGN_EXTEND_2 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let i : Nat := args[2]!.getIntegerValue!.toNat
    let j : Nat := args[3]!.getIntegerValue!.toNat
    return q(@Rewrite.merge_sign_extend_2 $w $x $i $j)
  | .BV_SIGN_EXTEND_EQ_CONST_1 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let m : Nat := args[2]!.getIntegerValue!.toNat
    let c : Nat := args[3]!.getIntegerValue!.toNat
    return q(@Rewrite.sign_extend_eq_const_1 $w $x $m $c)
  | .BV_SIGN_EXTEND_EQ_CONST_2 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let m : Nat := args[2]!.getIntegerValue!.toNat
    let c : Nat := args[3]!.getIntegerValue!.toNat
    return q(@Rewrite.sign_extend_eq_const_2 $w $x $m $c)
  | .BV_ZERO_EXTEND_EQ_CONST_1 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let m : Nat := args[2]!.getIntegerValue!.toNat
    let c : Nat := args[3]!.getIntegerValue!.toNat
    return q(@Rewrite.zero_extend_eq_const_1 $w $x $m $c)
  | .BV_ZERO_EXTEND_EQ_CONST_2 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let m : Nat := args[2]!.getIntegerValue!.toNat
    let c : Nat := args[3]!.getIntegerValue!.toNat
    return q(@Rewrite.zero_extend_eq_const_2 $w $x $m $c)
  | .BV_ZERO_EXTEND_ULT_CONST_1 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let m : Nat := args[2]!.getIntegerValue!.toNat
    let c : Nat := args[3]!.getIntegerValue!.toNat
    return q(@Rewrite.zero_extend_ult_const_1 $w $x $m $c)
  | .BV_ZERO_EXTEND_ULT_CONST_2 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let m : Nat := args[2]!.getIntegerValue!.toNat
    let c : Nat := args[3]!.getIntegerValue!.toNat
    return q(@Rewrite.zero_extend_ult_const_2 $w $x $m $c)
  | .BV_SIGN_EXTEND_ULT_CONST_1 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let m : Nat := args[2]!.getIntegerValue!.toNat
    let c : Nat := args[3]!.getIntegerValue!.toNat
    return q(@Rewrite.sign_extend_ult_const_1 $w $x $m $c)
  | .BV_SIGN_EXTEND_ULT_CONST_2 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let m : Nat := args[2]!.getIntegerValue!.toNat
    let c : Nat := args[3]!.getIntegerValue!.toNat
    return q(@Rewrite.sign_extend_ult_const_2 $w $x $m $c)
  | .BV_SIGN_EXTEND_ULT_CONST_3 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let m : Nat := args[2]!.getIntegerValue!.toNat
    let c : Nat := args[3]!.getIntegerValue!.toNat
    return q(@Rewrite.sign_extend_ult_const_3 $w $x $m $c)
  | .BV_SIGN_EXTEND_ULT_CONST_4 =>
    let w : Nat := args[1]!.getSort!.getBitVectorSize!.toNat
    let x : Q(BitVec $w) ← reconstructTerm args[1]!
    let m : Nat := args[2]!.getIntegerValue!.toNat
    let c : Nat := args[3]!.getIntegerValue!.toNat
    return q(@Rewrite.sign_extend_ult_const_4 $w $x $m $c)
  | _ => return none

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  let some h ← rewriteTheorem? pf.getRewriteRule! pf.getArguments | return none
  let some h ← proveHypotheses? h | return none
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
