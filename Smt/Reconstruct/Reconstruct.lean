import cvc5
import Lean
import Qq

import Mathlib.Data.Real.Archimedean

import Smt.Reconstruct.Builtin
import Smt.Reconstruct.Options
import Smt.Reconstruct.Prop
import Smt.Reconstruct.Quant
import Smt.Reconstruct.Rewrite
import Smt.Reconstruct.Timed
import Smt.Reconstruct.UF
import Smt.Reconstruct.Util

/-- Takes an array `xs` of free variables or metavariables and a term `e` that may contain those variables, and abstracts and binds them as existential quantifiers.

- if `usedOnly = true` then only variables that the expression body depends on will appear.
- if `usedLetOnly = true` same as `usedOnly` except for let-bound variables. (That is, local constants which have been assigned a value.)
 -/
def Lean.Meta.mkExistsFVars (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) (usedLetOnly : Bool := true) (binderInfoForMVars := BinderInfo.implicit) : MetaM Expr := do
  let e ← if xs.isEmpty then return e else liftMkBindingM <| MetavarContext.mkLambda xs e usedOnly usedLetOnly binderInfoForMVars
  addExists e xs.size
where
  addExists : Expr → Nat → MetaM Expr
    | .lam n t b i, m + 1 => do
      let b ← addExists b m
      mkAppM ``Exists #[.lam n t b i]
    | e, _ => pure e

namespace Smt.Reconstruct

open Lean hiding Rat mkRat
open Qq cvc5
open Smt.Reconstruct.Prop

def getFVarExpr! (n : Name) : MetaM Expr := do
  match (← getLCtx).findFromUserName? n with
  | some d => return d.toExpr
  | none   => throwError "unknown free variable '{n}'"

def getFVarOrConstExpr! (n : Name) : MetaM Expr := do
  match (← getLCtx).findFromUserName? n with
  | some d => return d.toExpr
  | none   =>
    let c ← getConstInfo n
    return .const c.name (c.numLevelParams.iterate (.zero :: ·) [])

def rconsSort (s : cvc5.Sort) : MetaM Expr := do match s.getKind with
  | .BOOLEAN_SORT => return q(Prop)
  | .INTERNAL_SORT_KIND
  | .UNINTERPRETED_SORT => getFVarOrConstExpr! s.getSymbol
  | .BITVECTOR_SORT =>
    let w : Nat := s.getBitVectorSize.val
    return q(Std.BitVec $w)
  | .INTEGER_SORT => return q(Int)
  | .REAL_SORT => return q(Real)
  | _ => return .const `sorry []

partial def rconsTerm (t : cvc5.Term) : MetaM Expr := do match t.getKind with
  | .VARIABLE => getFVarExpr! (getVariableName t)
  | .CONSTANT => getFVarOrConstExpr! t.getSymbol
  | .CONST_BOOLEAN => return if t.getBooleanValue then q(True) else q(False)
  | .NOT =>
    let b : Q(Prop) ← rconsTerm t[0]!
    return q(¬$b)
  | .IMPLIES =>
    let mut curr : Q(Prop) ← rconsTerm t[t.getNumChildren - 1]!
    for i in [1:t.getNumChildren] do
      let p : Q(Prop) ← rconsTerm t[t.getNumChildren - i - 1]!
      curr := q($p → $curr)
    return curr
  | .AND => rightAssocOp q(And) t
  | .OR => rightAssocOp q(Or) t
  | .XOR => rightAssocOp q(XOr) t
  | .EQUAL =>
    let α : Q(Type) ← rconsSort t[0]!.getSort
    let x : Q($α) ← rconsTerm t[0]!
    let y : Q($α) ← rconsTerm t[1]!
    return q($x = $y)
  | .DISTINCT =>
    let α : Q(Type) ← rconsSort t[0]!.getSort
    let x : Q($α) ← rconsTerm t[0]!
    let y : Q($α) ← rconsTerm t[1]!
    return q($x ≠ $y)
  | .ITE =>
    let α : Q(Type) ← rconsSort t.getSort
    let c : Q(Prop) ← rconsTerm t[0]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let x : Q($α) ← rconsTerm t[1]!
    let y : Q($α) ← rconsTerm t[2]!
    return q(@ite $α $c $h $x $y)
  | .FORALL =>
    let mut xs : Array (Name × (Array Expr → MetaM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => rconsSort x.getSort)
    Meta.withLocalDeclsD xs fun xs => do
      let b ← rconsTerm t[1]!
      Meta.mkForallFVars xs b
  | .EXISTS =>
    let mut xs : Array (Name × (Array Expr → MetaM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => rconsSort x.getSort)
    Meta.withLocalDeclsD xs fun xs => do
      let b ← rconsTerm t[1]!
      Meta.mkExistsFVars xs b
  | .LAMBDA =>
    let mut xs : Array (Name × (Array Expr → MetaM Expr)) := #[]
    for x in t[0]! do
      xs := xs.push (getVariableName x, fun _ => rconsSort x.getSort)
    Meta.withLocalDeclsD xs fun xs => do
      let b ← rconsTerm t[1]!
      Meta.mkLambdaFVars xs b
  | .HO_APPLY =>
    return .app (← rconsTerm t[0]!) (← rconsTerm t[1]!)
  | .APPLY_UF =>
    let mut curr ← rconsTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := .app curr (← rconsTerm t[i]!)
    return curr
  | .SKOLEM_FUN =>
    rconsSkolem t
  | .CONST_BITVECTOR =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let v : Nat := (t.getBitVectorValue 10).toNat!
    return q(Std.BitVec.ofNat $w $v)
  | .BITVECTOR_BITOF =>
    let w : Nat := t[0]!.getSort.getBitVectorSize.val
    let x : Q(Std.BitVec $w) ← rconsTerm t[0]!
    let i : Nat := t.getOp[0]!.getIntegerValue.toNat
    return q(«$x».getLsb $i = true)
  | .BITVECTOR_BB_TERM =>
    let w : Nat := t.getNumChildren
    let bs : Q(Std.BitVec 0) := q(.nil)
    let f (bs : Expr) (i : Nat) : MetaM Expr := do
      let p : Q(Prop) ← rconsTerm t[i]!
      let bs : Q(Std.BitVec $i) := bs
      let hp : Q(Decidable $p) ← synthDecidableInst t[i]!
      return q(@Std.BitVec.cons $i (@decide $p $hp) $bs)
    let bs : Q(Std.BitVec $w) ← (List.range w).foldlM f bs
    return q($bs)
  | .BITVECTOR_ADD =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(Std.BitVec $w) ← rconsTerm t[0]!
    let y : Q(Std.BitVec $w) ← rconsTerm t[1]!
    return q($x + $y)
  | .CONST_INTEGER =>
    let x : Int := t.getIntegerValue
    let x' : Q(Nat) := mkRawNatLit x.natAbs
    if x ≥ 0 then
      return q(OfNat.ofNat $x' : Int)
    else
      return q(-(OfNat.ofNat $x' : Int))
  | .CONST_RATIONAL =>
    let x : Rat := t.getRationalValue
    let num : Q(Real) := mkRealLit x.num.natAbs
    if x.den == 1 then
      if x.num ≥ 0 then
        return q($num)
      else
        return q(-$num)
    else
      let den : Q(Real) := mkRealLit x.den
      if x.num ≥ 0 then
        return q($num / $den)
      else
        return q(-$num / $den)
  | .NEG =>
    if t.getSort.isInteger then
      let x : Q(Int) ← rconsTerm t[0]!
      return q(-$x)
    else
      let x : Q(Real) ← rconsTerm t[0]!
      return q(-$x)
  | .SUB =>
    if t.getSort.isInteger then
      let x : Q(Int) ← rconsTerm t[0]!
      let y : Q(Int) ← rconsTerm t[1]!
      return q($x - $y)
    else
      let x : Q(Real) ← rconsTerm t[0]!
      let y : Q(Real) ← rconsTerm t[1]!
      return q($x - $y)
  | .ADD =>
    if t.getSort.isInteger then
      let x : Q(Int) ← rconsTerm t[0]!
      let y : Q(Int) ← rconsTerm t[1]!
      return q($x + $y)
    else
      let x : Q(Real) ← rconsTerm t[0]!
      let y : Q(Real) ← rconsTerm t[1]!
      return q($x + $y)
  | .MULT =>
    if t.getSort.isInteger then
      let x : Q(Int) ← rconsTerm t[0]!
      let y : Q(Int) ← rconsTerm t[1]!
      return q($x * $y)
    else
      let x : Q(Real) ← rconsTerm t[0]!
      let y : Q(Real) ← rconsTerm t[1]!
      return q($x * $y)
  | .INTS_DIVISION =>
    let x : Q(Int) ← rconsTerm t[0]!
    let y : Q(Int) ← rconsTerm t[1]!
    return q($x / $y)
  | .INTS_MODULUS =>
    let x : Q(Int) ← rconsTerm t[0]!
    let y : Q(Int) ← rconsTerm t[1]!
    return q($x % $y)
  | .DIVISION =>
    let x : Q(Real) ← rconsTerm t[0]!
    let y : Q(Real) ← rconsTerm t[1]!
    return q($x / $y)
  | .ABS =>
    let x : Q(Int) ← rconsTerm t[0]!
    return q(Int.natAbs $x : Int)
  | .LEQ =>
    if t[0]!.getSort.isInteger then
      let x : Q(Int) ← rconsTerm t[0]!
      let y : Q(Int) ← rconsTerm t[1]!
      return q($x ≤ $y)
    else
      let x : Q(Real) ← rconsTerm t[0]!
      let y : Q(Real) ← rconsTerm t[1]!
      return q($x ≤ $y)
  | .LT =>
    if t[0]!.getSort.isInteger then
      let x : Q(Int) ← rconsTerm t[0]!
      let y : Q(Int) ← rconsTerm t[1]!
      return q($x < $y)
    else
      let x : Q(Real) ← rconsTerm t[0]!
      let y : Q(Real) ← rconsTerm t[1]!
      return q($x < $y)
  | .GEQ =>
    if t[0]!.getSort.isInteger then
      let x : Q(Int) ← rconsTerm t[0]!
      let y : Q(Int) ← rconsTerm t[1]!
      return q($x ≥ $y)
    else
      let x : Q(Real) ← rconsTerm t[0]!
      let y : Q(Real) ← rconsTerm t[1]!
      return q($x ≥ $y)
  | .GT =>
    if t[0]!.getSort.isInteger then
      let x : Q(Int) ← rconsTerm t[0]!
      let y : Q(Int) ← rconsTerm t[1]!
      return q($x > $y)
    else
      let x : Q(Real) ← rconsTerm t[0]!
      let y : Q(Real) ← rconsTerm t[1]!
      return q($x > $y)
  | .TO_REAL =>
    let x : Q(Int) ← rconsTerm t[0]!
    return q($x : Real)
  | .TO_INTEGER =>
    let x : Q(Real) ← rconsTerm t[0]!
    return q(⌊$x⌋)
  | .IS_INTEGER =>
    let x : Q(Real) ← rconsTerm t[0]!
    return q($x = ⌊$x⌋)
  | _ =>
    throwError "Unsupported kind: {repr t.getKind} : {t}"
where
  mkRealLit (n : Nat) : Q(Real) := match h : n with
    | 0     => q(0 : Real)
    | 1     => q(1 : Real)
    | _ + 2 =>
      let h : Q(Nat.AtLeastTwo $n) := h ▸ q(instNatAtLeastTwo)
      let h := mkApp3 q(@instOfNat Real) (mkRawNatLit n) q(Real.natCast) h
      mkApp2 q(@OfNat.ofNat Real) (mkRawNatLit n) h
  rconsForallSkolems (q : cvc5.Term) (n : Nat) : MetaM (Array Expr) := do
    let mut xs : Array (Name × (Array Expr → MetaM Expr)) := #[]
    let mut es := #[]
    for x in q[0]![0]! do
      xs := xs.push (getVariableName x, fun _ => rconsSort x.getSort)
    let F := q[0]![1]!
    for i in [0:n + 1] do
      let α : Q(Type) ← rconsSort q[0]![0]![i]!.getSort
      let h : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
      let e ← Meta.withLocalDeclsD xs fun xs => do
        let F ← rconsTerm F
        let F' := F.replaceFVars xs[0:i] es
        let ysF' ← Meta.mkExistsFVars xs[i + 1:n] F'
        let xysF' : Q($α → Prop) ← Meta.mkLambdaFVars #[xs[i]!] (.app q(Not) ysF')
        return q(@Classical.epsilon $α $h $xysF')
      es := es.push e
    return es
  rconsExistsSkolems (q : cvc5.Term) (n : Nat) : MetaM (Array Expr) := do
    let mut xs : Array (Name × (Array Expr → MetaM Expr)) := #[]
    let mut es := #[]
    for x in q[0]! do
      xs := xs.push (getVariableName x, fun _ => rconsSort x.getSort)
    let F := q[1]!
    for i in [0:n + 1] do
      let α : Q(Type) ← rconsSort q[0]![i]!.getSort
      let h : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
      let e ← Meta.withLocalDeclsD xs fun xs => do
        let F ← rconsTerm F
        let F' := F.replaceFVars xs[0:i] es
        let ysF' ← Meta.mkExistsFVars xs[i + 1:n] F'
        let xysF' : Q($α → Prop) ← Meta.mkLambdaFVars #[xs[i]!] ysF'
        return q(@Classical.epsilon $α $h $xysF')
      es := es.push e
    return es
  rconsSkolem (t : cvc5.Term) : MetaM Expr := do match t.getSkolemId with
    | .PURIFY => rconsTerm t.getSkolemArguments[0]!
    | .DIV_BY_ZERO => return q(fun (x : Real) => x / 0)
    | .INT_DIV_BY_ZERO => return q(fun (x : Int) => x / 0)
    | .MOD_BY_ZERO => return q(fun (x : Int) => x % 0)
    | .QUANTIFIERS_SKOLEMIZE =>
      let q := t.getSkolemArguments[0]!
      let n := t.getSkolemArguments[1]!.getIntegerValue.toNat
      let es ← if q.getKind == .EXISTS then rconsExistsSkolems q n else rconsForallSkolems q n
      return es[n]!
    | _ =>
      throwError "Unsupported skolem ID: {repr t.getSkolemId} : {t.getSkolemArguments}"
  getVariableName (t : cvc5.Term) : Name :=
    if t.hasSymbol then t.getSymbol else Name.num `x t.getId
  rightAssocOp (op : Expr) (t : cvc5.Term) : MetaM Expr := do
    let mut curr ← rconsTerm t[t.getNumChildren - 1]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op (← rconsTerm t[t.getNumChildren - i - 1]!) curr
    return curr
  rightAssocOpDecidableInst (op : Expr) (inst : Expr) (t : cvc5.Term) : MetaM Expr := do
    let mut curr ← rconsTerm t[t.getNumChildren - 1]!
    let mut currInst ← synthDecidableInst t[t.getNumChildren - 1]!
    for i in [1:t.getNumChildren] do
      let ct := t[t.getNumChildren - i - 1]!
      currInst := mkApp4 inst (← rconsTerm ct) curr (← synthDecidableInst ct) currInst
      curr := mkApp2 op (← rconsTerm ct) curr
    return currInst
  synthDecidableInst (t : cvc5.Term) : MetaM Expr := do match t.getKind with
    | .CONST_BOOLEAN => return if t.getBooleanValue then q(instDecidableTrue) else q(instDecidableFalse)
    | .NOT =>
      let p : Q(Prop) ← rconsTerm t[0]!
      let hp : Q(Decidable $p) ← synthDecidableInst t[0]!
      return q(@instDecidableNot $p $hp)
    | .AND => rightAssocOpDecidableInst q(And) q(@instDecidableAnd) t
    | .OR => rightAssocOpDecidableInst q(Or) q(@instDecidableOr) t
    | .XOR => rightAssocOpDecidableInst q(XOr) q(@XOr.instDecidableXOr) t
    | .EQUAL =>
      if t[0]!.getSort.getKind == .BOOLEAN_SORT then
        let p : Q(Prop) ← rconsTerm t[0]!
        let q : Q(Prop) ← rconsTerm t[1]!
        let hp : Q(Decidable $p) ← synthDecidableInst t[0]!
        let hq : Q(Decidable $q) ← synthDecidableInst t[1]!
        return q(@instDecidableEqProp $p $q (@instDecidableIff $p $q $hp $hq))
      if t[0]!.getSort.getKind == .BITVECTOR_SORT then
        let w : Nat := t[0]!.getSort.getBitVectorSize.val
        return q(@Std.instDecidableEqBitVec $w)
      let p : Q(Prop) ← rconsTerm t
      Meta.synthInstance q(Decidable $p)
    | .BITVECTOR_BITOF =>
      let w : Nat := t[0]!.getSort.getBitVectorSize.val
      let x : Q(Std.BitVec $w) ← rconsTerm t[0]!
      let i : Nat := t.getOp[0]!.getIntegerValue.toNat
      return q(instDecidableEqBool («$x».getLsb $i) true)
    | _ =>
      let p : Q(Prop) ← rconsTerm t
      Meta.synthInstance q(Decidable $p)

structure RconsState where
  termMap : HashMap cvc5.Term Name
  proofMap : HashMap cvc5.Proof Name
  count : Nat
  trusts : Array cvc5.Proof
  mainGoal : MVarId
  currGoal : MVarId
  currAssums : Array Expr
  skipedGoals : Array MVarId

abbrev RconsM := StateT RconsState MetaM

namespace Rcons

def incCount : RconsM Nat :=
  modifyGet fun state => (state.count, { state with count := state.count + 1 })

def cacheTerm (t : cvc5.Term) (n : Name) : RconsM Unit :=
  modify fun state => { state with termMap := state.termMap.insert t n }

def getTermExpr (t : cvc5.Term) : RconsM Expr :=
  return .fvar ⟨(← get).termMap.find! t⟩

def cacheProof (pf : cvc5.Proof) (n : Name) : RconsM Unit :=
  modify fun state => { state with proofMap := state.proofMap.insert pf n }

def isReconstructed (pf : cvc5.Proof) : RconsM Bool := do
  let state ← get
  if !state.proofMap.contains pf then
    return false
  state.currGoal.withContext do
    let ctx ← getLCtx
    return if ctx.contains ⟨state.proofMap.find! pf⟩ then true else false

def getProofExpr (pf : cvc5.Proof) : RconsM Expr :=
  return .fvar ⟨(← get).proofMap.find! pf⟩

def withAssums (as : Array Expr) (k : RconsM α) : RconsM α := do
  modify fun state => { state with currAssums := state.currAssums ++ as }
  let r ← k
  modify fun state => { state with currAssums := state.currAssums.shrink (state.currAssums.size - as.size) }
  return r

def skipStep (mv : MVarId) : RconsM Unit := mv.withContext do
  let state ← get
  let t ← Meta.mkForallFVars state.currAssums (← mv.getType)
  let mv' ← state.mainGoal.withContext (Meta.mkFreshExprMVar t)
  let e := mkAppN mv' state.currAssums
  set { state with skipedGoals := state.skipedGoals.push mv'.mvarId! }
  mv.assignIfDefeq e

inductive Tac where
  | rewrite : Expr → Expr → Expr → Array (Array Expr) → Tac
  | r0 : Expr → Expr → Expr → Option Nat → Option Nat → Tac
  | r1 : Expr → Expr → Expr → Option Nat → Option Nat → Tac
  | factor : Expr → Option Nat → Tac
  | reorder : Expr → Array Nat → Option Nat → Tac
  | andElim : Expr → Nat → Tac
  | notOrElim : Expr → Nat → Tac
  | cong : Array Expr → Tac
  | sumUB : Array Expr → Tac
  | polyNorm : Tac
  | mulSign : Array (Expr × Fin 3 × Nat) → Tac
deriving Repr

instance : ToMessageData Tac where
  toMessageData : Tac → MessageData
    | .rewrite assoc null rule args => m!"rewrite {assoc} {null} {rule} {args}"
    | .r0 v₁ v₂ p i₁ i₂ => m!"r0 {v₁} {v₂} ({p}) {i₁} {i₂}"
    | .r1 v₁ v₂ p i₁ i₂ => m!"r1 {v₁} {v₂} ({p}) {i₁} {i₂}"
    | .factor v i => m!"factor {v} {i}"
    | .reorder n is i => m!"reorder {n} {is} {i}"
    | .andElim n i => m!"andElim {n} {i}"
    | .notOrElim n i => m!"notOrElim {n} {i}"
    | .cong ns => m!"cong {ns}"
    | .sumUB ns => m!"sumUB {ns}"
    | .polyNorm => m!"polyNorm"
    | .mulSign fs => m!"mulSign {fs}"

def runTac (mv : MVarId) (tac : Tac) : RconsM Unit := mv.withContext do
  match tac with
  | .rewrite assoc null rule args => Tactic.smtRw mv assoc null rule args
  | .r0 v₁ v₂ p i₁ i₂ => r₀ mv v₁ v₂ p i₁ i₂
  | .r1 v₁ v₂ p i₁ i₂ => r₁ mv v₁ v₂ p i₁ i₂
  | .factor v i => factor mv v i
  | .reorder e is i => reorder mv e is i
  | .andElim e i => andElim mv e i
  | .notOrElim e i => notOrElim mv e i
  | .cong es => UF.smtCongr mv es
  | .sumUB _ => skipStep mv
  | .polyNorm => skipStep mv
  | .mulSign _ => skipStep mv

def getCurrGoal : RconsM MVarId :=
  get >>= (pure ·.currGoal)

def setCurrGoal (mv : MVarId) : RconsM Unit :=
  modify fun state => { state with currGoal := mv }

def addThm (type : Expr) (val : Expr) : RconsM Expr := do
  let mv ← getCurrGoal
  mv.withContext do
    let name := Name.num `s (← incCount)
    let (fv, mv) ← (← mv.assert name type val).intro1P
    trace[smt.debug.reconstruct] "have {name} : {type} := {val}"
    setCurrGoal mv
    return .fvar fv

def addTac (type : Expr) (tac : Tac) : RconsM Expr := do
  let mv ← getCurrGoal
  mv.withContext do
    let name := Name.num `s (← incCount)
    let mv' ← Meta.mkFreshExprMVar type
    runTac mv'.mvarId! tac
    let (fv, mv) ← (← mv.assert name type mv').intro1P
    trace[smt.debug.reconstruct] "have {name} : {type} := by {tac}"
    setCurrGoal mv
    return .fvar fv

def addTrust (type : Expr) (pf : cvc5.Proof) : RconsM Expr := do
  let mv ← getCurrGoal
  mv.withContext do
    let name := Name.num `s (← incCount)
    let mv' ← Meta.mkFreshExprMVar type
    skipStep mv'.mvarId!
    let (fv, mv) ← (← mv.assert name type mv').intro1P
    trace[smt.debug.reconstruct] m!"have {name} : {type} := sorry"
    trace[smt.debug.reconstruct]
      m!"rule : {repr pf.getRule}\npremises : {pf.getChildren.map (·.getResult)}\nargs : {pf.getArguments}\nconclusion : {pf.getResult}"
    modify fun state => { state with trusts := state.trusts.push pf }
    setCurrGoal mv
    return .fvar fv

def rconsRewrite (pf : cvc5.Proof) (cpfs : Array Expr) : RconsM Expr := do
  match cvc5.RewriteRule.fromNat! pf.getArguments[0]!.getIntegerValue.toNat with
  | .BOOL_DOUBLE_NOT_ELIM =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[1]!
    addThm q((¬¬$p) = $p) q(@Prop.bool_double_not_elim $p)
  | .BOOL_EQ_TRUE =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[1]!
    addThm q(($p = True) = $p) q(@Prop.bool_eq_true $p)
  | .BOOL_EQ_FALSE =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[1]!
    addThm q(($p = False) = ¬$p) q(@Prop.bool_eq_false $p)
  | .BOOL_EQ_NREFL =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[1]!
    addThm q(($p = ¬$p) = False) q(@Prop.bool_eq_nrefl $p)
  | .BOOL_IMPL_FALSE1 =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[1]!
    addThm q(($p → False) = ¬$p) q(@Prop.bool_impl_false1 $p)
  | .BOOL_IMPL_FALSE2 =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[1]!
    addThm q((False → $p) = True) q(@Prop.bool_impl_false2 $p)
  | .BOOL_IMPL_TRUE1 =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[1]!
    addThm q(($p → True) = True) q(@Prop.bool_impl_true1 $p)
  | .BOOL_IMPL_TRUE2 =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[1]!
    addThm q((True → $p) = $p) q(@Prop.bool_impl_true2 $p)
  -- | .BOOL_OR_TRUE =>
  --   let args ← rconsArgs pf.getArguments
  --   addTac (← rconsTerm pf.getResult) (.rewrite q(@Prop.or_assoc_eq) q(or_false) q(@Prop.bool_or_true) args)
  | .BOOL_OR_FALSE =>
    let args ← rconsArgs pf.getArguments
    addTac (← rconsTerm pf.getResult) (.rewrite q(@Prop.or_assoc_eq) q(or_false) q(@Prop.bool_or_false) args)
  | .BOOL_OR_FLATTEN =>
    let args ← rconsArgs pf.getArguments
    addTac (← rconsTerm pf.getResult) (.rewrite q(@Prop.or_assoc_eq) q(or_false) q(@Prop.bool_or_flatten) args)
  | .BOOL_OR_DUP =>
    let args ← rconsArgs pf.getArguments
    addTac (← rconsTerm pf.getResult) (.rewrite q(@Prop.or_assoc_eq) q(or_false) q(@Prop.bool_or_dup) args)
  | .BOOL_AND_TRUE =>
    let args ← rconsArgs pf.getArguments
    addTac (← rconsTerm pf.getResult) (.rewrite q(@Prop.and_assoc_eq) q(and_true) q(@Prop.bool_and_true) args)
  -- | .BOOL_AND_FALSE =>
  --   let args ← rconsArgs pf.getArguments
  --   addTac (← rconsTerm pf.getResult) (.rewrite q(@Prop.and_assoc_eq) q(and_true) q(@Prop.bool_and_false) args)
  | .BOOL_AND_FLATTEN =>
    let args ← rconsArgs pf.getArguments
    addTac (← rconsTerm pf.getResult) (.rewrite q(@Prop.and_assoc_eq) q(and_true) q(@Prop.bool_and_flatten) args)
  | .BOOL_AND_DUP =>
    let args ← rconsArgs pf.getArguments
    addTac (← rconsTerm pf.getResult) (.rewrite q(@Prop.and_assoc_eq) q(and_true) q(@Prop.bool_and_dup) args)
  | .BOOL_AND_CONF =>
    let args ← rconsArgs pf.getArguments
    addTac (← rconsTerm pf.getResult) (.rewrite q(@Prop.and_assoc_eq) q(and_true) q(@Prop.bool_and_conf) args)
  | .BOOL_OR_TAUT =>
    let args ← rconsArgs pf.getArguments
    addTac (← rconsTerm pf.getResult) (.rewrite q(@Prop.or_assoc_eq) q(or_false) q(@Prop.bool_or_taut) args)
  | .BOOL_XOR_REFL =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[1]!
    addThm q(XOr $p $p = False) q(@Prop.bool_xor_refl $p)
  | .BOOL_XOR_NREFL =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[1]!
    addThm q((XOr $p ¬$p) = True) q(@Prop.bool_xor_nrefl $p)
  | .BOOL_XOR_FALSE =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[1]!
    addThm q(XOr $p False = $p) q(@Prop.bool_xor_false $p)
  | .BOOL_XOR_TRUE =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[1]!
    addThm q(XOr $p True = ¬$p) q(@Prop.bool_xor_true $p)
  | .BOOL_XOR_COMM =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[2]!
    addThm q(XOr $p $q = XOr $q $p) q(@Prop.bool_xor_comm $p $q)
  | .BOOL_XOR_ELIM =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[2]!
    addThm q(XOr $p $q = ¬($p = $q)) q(@Prop.bool_xor_elim $p $q)
  | .ITE_NEG_BRANCH =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let p : Q(Prop) ← rconsTerm pf.getArguments[2]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[3]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let h : Q($p = ¬$q) := cpfs[0]!
    addThm q(ite $c $p $q = ($c = $p)) q(@Prop.ite_neg_branch $c $p $q $hc $h)
  | .ITE_THEN_TRUE =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let p : Q(Prop) ← rconsTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c True $p = ($c ∨ $p)) q(@Prop.ite_then_true $c $p $h)
  | .ITE_ELSE_FALSE =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let p : Q(Prop) ← rconsTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $p False = ($c ∧ $p)) q(@Prop.ite_else_false $c $p $h)
  | .ITE_THEN_FALSE =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let p : Q(Prop) ← rconsTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c False $p = (¬$c ∧ $p)) q(@Prop.ite_then_false $c $p $h)
  | .ITE_ELSE_TRUE =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let p : Q(Prop) ← rconsTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $p True = (¬$c ∨ $p)) q(@Prop.ite_else_true $c $p $h)
  | .ITE_THEN_LOOKAHEAD_SELF =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let p : Q(Prop) ← rconsTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $c $p = ite $c True $p) q(@Prop.ite_then_lookahead_self $c $p $h)
  | .ITE_ELSE_LOOKAHEAD_SELF =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let p : Q(Prop) ← rconsTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $p $c = ite $c $p False) q(@Prop.ite_else_lookahead_self $c $p $h)
  | .ITE_TRUE_COND =>
    let α : Q(Type) ← rconsSort pf.getArguments[1]!.getSort
    let x : Q($α) ← rconsTerm pf.getArguments[1]!
    let y : Q($α) ← rconsTerm pf.getArguments[2]!
    addThm q(ite True $x $y = $x) q(@Builtin.ite_true_cond $α $x $y)
  | .ITE_FALSE_COND =>
    let α : Q(Type) ← rconsSort pf.getArguments[1]!.getSort
    let x : Q($α) ← rconsTerm pf.getArguments[1]!
    let y : Q($α) ← rconsTerm pf.getArguments[2]!
    addThm q(ite False $x $y = $y) q(@Builtin.ite_false_cond $α $x $y)
  | .ITE_NOT_COND =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let α : Q(Type) ← rconsSort pf.getArguments[2]!.getSort
    let x : Q($α) ← rconsTerm pf.getArguments[2]!
    let y : Q($α) ← rconsTerm pf.getArguments[3]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite (¬$c) $x $y = ite $c $y $x) q(@Builtin.ite_not_cond $c $α $x $y $h)
  | .ITE_EQ_BRANCH =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let α : Q(Type) ← rconsSort pf.getArguments[2]!.getSort
    let x : Q($α) ← rconsTerm pf.getArguments[2]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $x $x = $x) q(@Builtin.ite_eq_branch $c $α $x $h)
  | .ITE_THEN_LOOKAHEAD =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let α : Q(Type) ← rconsSort pf.getArguments[2]!.getSort
    let x : Q($α) ← rconsTerm pf.getArguments[2]!
    let y : Q($α) ← rconsTerm pf.getArguments[3]!
    let z : Q($α) ← rconsTerm pf.getArguments[4]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c (ite $c $x $y) $z = ite $c $x $z) q(@Builtin.ite_then_lookahead $c $α $x $y $z $h)
  | .ITE_ELSE_LOOKAHEAD =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let α : Q(Type) ← rconsSort pf.getArguments[2]!.getSort
    let x : Q($α) ← rconsTerm pf.getArguments[2]!
    let y : Q($α) ← rconsTerm pf.getArguments[3]!
    let z : Q($α) ← rconsTerm pf.getArguments[4]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $x (ite $c $y $z) = ite $c $x $z) q(@Builtin.ite_else_lookahead $c $α $x $y $z $h)
  | .ITE_THEN_NEG_LOOKAHEAD =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let α : Q(Type) ← rconsSort pf.getArguments[2]!.getSort
    let x : Q($α) ← rconsTerm pf.getArguments[2]!
    let y : Q($α) ← rconsTerm pf.getArguments[3]!
    let z : Q($α) ← rconsTerm pf.getArguments[4]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c (ite (¬$c) $x $y) $z = ite $c $y $z) q(@Builtin.ite_then_neg_lookahead $c $α $x $y $z $h)
  | .ITE_ELSE_NEG_LOOKAHEAD =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[1]!
    let α : Q(Type) ← rconsSort pf.getArguments[2]!.getSort
    let x : Q($α) ← rconsTerm pf.getArguments[2]!
    let y : Q($α) ← rconsTerm pf.getArguments[3]!
    let z : Q($α) ← rconsTerm pf.getArguments[4]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    addThm q(ite $c $x (ite (¬$c) $y $z) = ite $c $x $y) q(@Builtin.ite_else_neg_lookahead $c $α $x $y $z $h)
  | .EQ_REFL =>
    let α : Q(Type) ← rconsSort pf.getArguments[1]!.getSort
    let t : Q($α) ← rconsTerm pf.getArguments[1]!
    addThm q(($t = $t) = True) q(@UF.eq_refl $α $t)
  | .EQ_SYMM =>
    let α : Q(Type) ← rconsSort pf.getArguments[1]!.getSort
    let t : Q($α) ← rconsTerm pf.getArguments[1]!
    let s : Q($α) ← rconsTerm pf.getArguments[2]!
    addThm q(($t = $s) = ($s = $t)) q(@UF.eq_symm $α $t $s)
  | .DISTINCT_BINARY_ELIM =>
    let α : Q(Type) ← rconsSort pf.getArguments[1]!.getSort
    let t : Q($α) ← rconsTerm pf.getArguments[1]!
    let s : Q($α) ← rconsTerm pf.getArguments[2]!
    addThm q(($t ≠ $s) = ¬($t = $s)) q(@UF.distinct_binary_elim $α $t $s)
  | _ =>
    let type ← rconsTerm pf.getResult
    addTrust type pf
where
  rconsArgs (args : Array cvc5.Term) : MetaM (Array (Array Expr)) := do
    let mut args' := #[]
    for arg in args do
      let mut arg' := #[]
      for subarg in arg do
        arg' := arg'.push (← rconsTerm subarg)
      args' := args'.push arg'
    return args'

def getResolutionResult (c₁ c₂ : Array cvc5.Term) (pol l : cvc5.Term) : Array cvc5.Term := Id.run do
  let l₁ := if pol.getBooleanValue then l else l.not
  let l₂ := if pol.getBooleanValue then l.not else l
  let mut ls := #[]
  for li in c₁ do
    if li != l₁ then
      ls := ls.push li
  for li in c₂ do
    if li != l₂ then
      ls := ls.push li
  return ls

def rconsResolution (c₁ c₂ : Array cvc5.Term) (pol l : cvc5.Term) (p₁ p₂ : Expr) : RconsM Expr := do
  let f := if pol.getBooleanValue == true then Tac.r0 else Tac.r1
  addTac (← rightAssocOp q(Or) (getResolutionResult c₁ c₂ pol l)) (f p₁ p₂ (← rconsTerm l) (some (c₁.size - 1)) (some (c₂.size - 1)))
where
  rightAssocOp (op : Expr) (ts : Array cvc5.Term) : MetaM Expr := do
    if ts.isEmpty then
      return q(False)
    let mut curr ← rconsTerm ts[ts.size - 1]!
    for i in [1:ts.size] do
      curr := mkApp2 op (← rconsTerm ts[ts.size - i - 1]!) curr
    return curr

def clausify (c : cvc5.Term) : Array cvc5.Term := Id.run do
  if c.getKind != .OR then
    return #[c]
  let mut cs := #[]
  for cc in c do
    cs := cs.push cc
  return cs

def rconsChainResolution (cs as : Array cvc5.Term) (ps : Array Expr) : RconsM Expr := do
  let mut cc := clausify cs[0]!
  let mut cp := ps[0]!
  for i in [1:cs.size] do
    let pol := as[0]![i - 1]!
    let l := as[1]![i - 1]!
    cp ← rconsResolution cc (clausify cs[i]!) pol l cp ps[i]!
    cc := getResolutionResult cc (clausify cs[i]!) pol l
  return cp

def rconsScope (pf : cvc5.Proof) (rconsProof : cvc5.Proof → RconsM Expr) : RconsM Expr := do
  let mv ← getCurrGoal
  mv.withContext do
    let f := fun arg ps => do
      let p : Q(Prop) ← rconsTerm arg
      return q($p :: $ps)
    let ps : Q(List Prop) ← pf.getArguments.foldrM f q([])
    let as ← pf.getArguments.mapM (fun _ => return Name.num `a (← incCount))
    let q : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult
    let h₁ : Q(impliesN $ps $q) ← Meta.mkFreshExprMVar q(impliesN $ps $q)
    let (fvs, mv') ← h₁.mvarId!.introN pf.getArguments.size as.toList
    setCurrGoal mv'
    mv'.withContext do
      let h₂ : Q($q) ← withAssums (fvs.map Expr.fvar) (rconsProof pf.getChildren[0]!)
      let mv'' ← getCurrGoal
      mv''.withContext (mv''.assignIfDefeq h₂)
    setCurrGoal mv
    addThm q(andN $ps → $q) q(Prop.scopes $h₁)

def rconsForallCong (pf : cvc5.Proof) (rconsProof : cvc5.Proof → RconsM Expr) : RconsM Expr := do
  let mv ← getCurrGoal
  mv.withContext do
    let n := rconsTerm.getVariableName pf.getArguments[1]![0]!
    let α : Q(Type) ← rconsSort pf.getArguments[1]![0]!.getSort
    let mkLam n α t := Meta.withLocalDeclD n α (rconsTerm t >>= Meta.mkLambdaFVars #[·])
    let p : Q($α → Prop) ← mkLam n α pf.getResult[0]![1]!
    let q : Q($α → Prop) ← mkLam n α pf.getResult[1]![1]!
    let h : Q(∀ a, $p a = $q a) ← Meta.mkFreshExprMVar q(∀ a, $p a = $q a)
    let (fv, mv') ← h.mvarId!.intro n
    let a : Q($α) ← (return .fvar fv)
    setCurrGoal mv'
    let h' : Q($p $a = $q $a) ← mv'.withContext (withAssums #[a] (rconsProof pf.getChildren[0]!))
    let mv' ← getCurrGoal
    mv'.withContext (mv'.assignIfDefeq h')
    setCurrGoal mv
    addThm q((∀ a, $p a) = (∀ a, $q a)) q(forall_congr $h)

def rconsBB (pf : cvc5.Proof) : RconsM Expr := do
  let t := pf.getArguments[0]![0]!
  match t.getKind with
  | .CONST_BITVECTOR =>
    let w : Nat := t.getSort.getBitVectorSize.toNat
    let t : Q(Std.BitVec $w) ← rconsTerm pf.getResult[0]!
    let t' : Q(Std.BitVec $w) ← rconsTerm pf.getResult[1]!
    addThm q($t = $t') q(Eq.refl $t)
  | _ =>
    let type ← rconsTerm pf.getResult
    addTrust type pf

def rconsSkolemize (pf : cvc5.Proof) (rconsProof : cvc5.Proof → RconsM Expr) : RconsM Expr := do
  if pf.getChildren[0]!.getResult.getKind == .EXISTS then
    let es ← rconsTerm.rconsExistsSkolems pf.getChildren[0]!.getResult (pf.getChildren[0]!.getResult[0]![0]!.getNumChildren - 1)
    let f := fun h e => do
      let α : Q(Type) ← pure (e.getArg! 0)
      let hα : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
      let p : Q($α → Prop)  ← pure (e.getArg! 2)
      let h : Q(∃ x, $p x) ← pure h
      return q(@Classical.epsilon_spec_aux $α $hα $p $h)
    let h : Expr ← es.foldlM f (← rconsProof pf.getChildren[0]!)
    addThm (← rconsTerm pf.getResult) h
  else
    let es ← rconsTerm.rconsForallSkolems pf.getChildren[0]!.getResult (pf.getChildren[0]!.getResult[0]![0]!.getNumChildren - 1)
    let f := fun h e => do
      let α : Q(Type) ← pure (e.getArg! 0)
      let hα : Q(Nonempty $α) ← Meta.synthInstance q(Nonempty $α)
      let .lam n _ (.app _ b) bi := e.getArg! 2 | throwError "[skolemize]: expected a predicate with a negated body: {e}"
      let p : Q($α → Prop)  ← pure (.lam n α b bi)
      let h : Q(¬∀ x, $p x) ← pure h
      return q(@Classical.epsilon_spec_aux' $α $hα $p $h)
    let h : Expr ← es.foldlM f (← rconsProof pf.getChildren[0]!)
    addThm (← rconsTerm pf.getResult) h

partial def rconsProof (pf : cvc5.Proof) : RconsM Expr := do
  if ← isReconstructed pf then
    return ← getProofExpr pf
  let e ← do match pf.getRule with
  | .ASSUME =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]!
    match (← Meta.findLocalDeclWithType? p) with
    | none => throwError "no assumption of type\n\t{p}\nfound in local context"
    | some fv => return .fvar fv
  | .SCOPE =>
    rconsScope pf rconsProof
  | .EVALUATE =>
    let α : Q(Type) ← rconsSort pf.getResult[0]!.getSort
    -- TODO: handle case where a Prop is inside an expression
    if α.isProp then
      let p  : Q(Prop) ← rconsTerm pf.getResult[0]!
      let p' : Q(Prop) ← rconsTerm pf.getResult[1]!
      addThm q($p = $p') (← Meta.mkAppOptM ``of_decide_eq_true #[q($p = $p'), none, q(Eq.refl true)])
    else
      let t  : Q($α) ← rconsTerm pf.getResult[0]!
      let t' : Q($α) ← rconsTerm pf.getResult[1]!
      addThm q($t = $t') q(Eq.refl $t)
  | .DSL_REWRITE =>
    rconsRewrite pf (← pf.getChildren.mapM rconsProof)
  | .RESOLUTION =>
    let c₁ := clausify pf.getChildren[0]!.getResult
    let c₂ := clausify pf.getChildren[1]!.getResult
    let p₁ ← rconsProof pf.getChildren[0]!
    let p₂ ← rconsProof pf.getChildren[1]!
    rconsResolution c₁ c₂ pf.getArguments[0]! pf.getArguments[1]! p₁ p₂
  | .CHAIN_RESOLUTION =>
    let cs := pf.getChildren.map (·.getResult)
    let as := pf.getArguments
    let ps ← pf.getChildren.mapM rconsProof
    rconsChainResolution cs as ps
  | .FACTORING =>
    -- as an argument we pass whether the suffix of the factoring clause is a
    -- singleton *repeated* literal. This is marked by a number as in
    -- resolution.
    let children := pf.getChildren
    let lastPremiseLit := children[0]!.getResult[children[0]!.getResult.getNumChildren - 1]!
    let resOriginal := pf.getResult
    -- For the last premise literal to be a singleton repeated literal, either
    -- it is equal to the result (in which case the premise was just n
    -- occurrences of it), or the end of the original clause is different from
    -- the end of the resulting one. In principle we'd need to add the
    -- singleton information only for OR nodes, so we could avoid this test if
    -- the result is not an OR node. However given the presence of
    -- purification boolean variables which can stand for OR nodes (and could
    -- thus be ambiguous in the final step, with the purification remove), we
    -- do the general test.
    let singleton := if lastPremiseLit == resOriginal || (resOriginal.getKind == .OR && lastPremiseLit != resOriginal[resOriginal.getNumChildren - 1]!)
      then some (children[0]!.getResult.getNumChildren - 1) else none;
    addTac (← rconsTerm pf.getResult) (.factor (← rconsProof children[0]!) singleton)
  | .REORDERING =>
    let children := pf.getChildren
    let size := pf.getResult.getNumChildren
    let lastPremiseLit := children[0]!.getResult[size - 1]!
    -- none if tail of the clause is not an OR (i.e., it cannot be a singleton)
    let singleton := if lastPremiseLit.getKind == .OR then some (size - 1) else none
    -- for each literal in the resulting clause, get its position in the premise
    let mut pos := #[]
    for resLit in pf.getResult do
      for i in [:size] do
        if children[0]!.getResult[i]! == resLit then
          pos := pos.push i
    -- turn conclusion into clause
    addTac (← rconsTerm pf.getResult) (.reorder (← rconsProof children[0]!) pos singleton)
  | .SPLIT =>
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]!
    addThm q($q ∨ ¬$q) q(Classical.em $q)
  | .EQ_RESOLVE =>
    let p : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult
    let q : Q(Prop) ← rconsTerm pf.getResult
    let hp : Q($p) ← rconsProof pf.getChildren[0]!
    let hpq : Q($p = $q) ← rconsProof pf.getChildren[1]!
    addThm q($q) q(Prop.eqResolve $hp $hpq)
  | .MODUS_PONENS =>
    let p : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult
    let q : Q(Prop) ← rconsTerm pf.getResult
    let hp : Q($p) ← rconsProof pf.getChildren[0]!
    let hpq : Q($p → $q) ← rconsProof pf.getChildren[1]!
    addThm q($q) q(Prop.modusPonens $hp $hpq)
  | .NOT_NOT_ELIM =>
    let p : Q(Prop) ← rconsTerm pf.getResult
    let hnnp : Q(¬¬$p) ← rconsProof pf.getChildren[0]!
    addThm q($p) q(Prop.notNotElim $hnnp)
  | .CONTRA =>
    let p : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult
    let hp : Q($p) ← rconsProof pf.getChildren[0]!
    let hnp : Q(¬$p) ← rconsProof pf.getChildren[0]!
    addThm q(False) q(Prop.contradiction $hp $hnp)
  | .AND_ELIM =>
    addTac (← rconsTerm pf.getResult) (.andElim (← rconsProof pf.getChildren[0]!) pf.getArguments[0]!.getIntegerValue.toNat)
  | .AND_INTRO =>
    let cpfs := pf.getChildren
    let q : Q(Prop) ← rconsTerm cpfs.back.getResult
    let hq : Q($q) ← rconsProof cpfs.back
    let f := fun pf ⟨q, hq⟩ => do
      let p : Q(Prop) ← rconsTerm pf.getResult
      let hp : Q($p) ← rconsProof pf
      let hq ← addThm q($p ∧ $q) q(And.intro $hp $hq)
      let q := q($p ∧ $q)
      return ⟨q, hq⟩
    let ⟨_, hq⟩ ← cpfs.pop.foldrM f (⟨q, hq⟩ : Σ q : Q(Prop), Q($q))
    return hq
  | .NOT_OR_ELIM =>
    addTac (← rconsTerm pf.getResult) (.notOrElim (← rconsProof pf.getChildren[0]!) pf.getArguments[0]!.getIntegerValue.toNat)
  | .IMPLIES_ELIM =>
    let p : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[0]!
    let q : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[1]!
    let hpq : Q($p → $q) ← rconsProof pf.getChildren[0]!
    addThm q(¬$p ∨ $q) q(Prop.impliesElim $hpq)
  | .NOT_IMPLIES_ELIM1 =>
    let p : Q(Prop) ← rconsTerm pf.getResult
    let q : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[0]![1]!
    let hnpq : Q(¬($p → $q)) ← rconsProof pf.getChildren[0]!
    addThm q($p) q(Prop.notImplies1 $hnpq)
  | .NOT_IMPLIES_ELIM2 =>
    let p : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getResult[0]!
    let hnpq : Q(¬($p → $q)) ← rconsProof pf.getChildren[0]!
    addThm q(¬$q) q(Prop.notImplies2 $hnpq)
  | .EQUIV_ELIM1 =>
    let p : Q(Prop) ← rconsTerm pf.getResult[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getResult[1]!
    let hpq : Q($p = $q) ← rconsProof pf.getChildren[0]!
    addThm q(¬$p ∨ $q) q(Prop.equivElim1 $hpq)
  | .EQUIV_ELIM2 =>
    let p : Q(Prop) ← rconsTerm pf.getResult[0]!
    let q : Q(Prop) ← rconsTerm pf.getResult[1]![0]!
    let hpq : Q($p = $q) ← rconsProof pf.getChildren[0]!
    addThm q($p ∨ ¬$q) q(Prop.equivElim2 $hpq)
  | .NOT_EQUIV_ELIM1 =>
    let p : Q(Prop) ← rconsTerm pf.getResult[0]!
    let q : Q(Prop) ← rconsTerm pf.getResult[1]!
    let hnpq : Q($p ≠ $q) ← rconsProof pf.getChildren[0]!
    addThm q($p ∨ $q) q(Prop.notEquivElim1 $hnpq)
  | .NOT_EQUIV_ELIM2 =>
    let p : Q(Prop) ← rconsTerm pf.getResult[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getResult[1]![0]!
    let hnpq : Q($p ≠ $q) ← rconsProof pf.getChildren[0]!
    addThm q(¬$p ∨ ¬$q) q(Prop.notEquivElim2 $hnpq)
  | .XOR_ELIM1 =>
    let p : Q(Prop) ← rconsTerm pf.getResult[0]!
    let q : Q(Prop) ← rconsTerm pf.getResult[1]!
    let hpq : Q(XOr $p $q) ← rconsProof pf.getChildren[0]!
    addThm q($p ∨ $q) q(Prop.xorElim1 $hpq)
  | .XOR_ELIM2 =>
    let p : Q(Prop) ← rconsTerm pf.getResult[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getResult[1]![0]!
    let hpq : Q(XOr $p $q) ← rconsProof pf.getChildren[0]!
    addThm q(¬$p ∨ ¬$q) q(Prop.xorElim2 $hpq)
  | .NOT_XOR_ELIM1 =>
    let p : Q(Prop) ← rconsTerm pf.getResult[0]!
    let q : Q(Prop) ← rconsTerm pf.getResult[1]![0]!
    let hnpq : Q(¬XOr $p $q) ← rconsProof pf.getChildren[0]!
    addThm q($p ∨ ¬$q) q(Prop.notXorElim1 $hnpq)
  | .NOT_XOR_ELIM2 =>
    let p : Q(Prop) ← rconsTerm pf.getResult[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getResult[1]!
    let hnpq : Q(¬XOr $p $q) ← rconsProof pf.getChildren[0]!
    addThm q(¬$p ∨ $q) q(Prop.notXorElim2 $hnpq)
  | .ITE_ELIM1 =>
    let c : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[0]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[1]!
    let q : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[2]!
    let h : Q(@ite Prop $c $hc $p $q) ← rconsProof pf.getChildren[0]!
    addThm q(¬$c ∨ $p) q(Prop.iteElim1 $h)
  | .ITE_ELIM2 =>
    let c : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[0]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[1]!
    let q : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[2]!
    let h : Q(@ite Prop $c $hc $p $q) ← rconsProof pf.getChildren[0]!
    addThm q($c ∨ $q) q(Prop.iteElim2 $h)
  | .NOT_ITE_ELIM1 =>
    let c : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[0]![0]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[0]![1]!
    let q : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[0]![2]!
    let hn : Q(¬@ite Prop $c $hc $p $q) ← rconsProof pf.getChildren[0]!
    addThm q(¬$c ∨ ¬$p) q(Prop.notIteElim1 $hn)
  | .NOT_ITE_ELIM2 =>
    let c : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[0]![0]!
    let hc : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[0]![1]!
    let q : Q(Prop) ← rconsTerm pf.getChildren[0]!.getResult[0]![2]!
    let hn : Q(¬@ite Prop $c $hc $p $q) ← rconsProof pf.getChildren[0]!
    addThm q($c ∨ ¬$q) q(Prop.notIteElim2 $hn)
  | .NOT_AND =>
    let fs := pf.getChildren[0]!.getResult[0]!
    let mut ps : Q(List Prop) := q([])
    let n := fs.getNumChildren
    for i in [:n] do
      let p : Q(Prop) ← rconsTerm fs[n - i - 1]!
      ps := q($p :: $ps)
    let hnps : Q(¬andN $ps) ← rconsProof pf.getChildren[0]!
    addThm (← rconsTerm pf.getResult) (.app q(Prop.notAnd $ps) hnps)
  | .CNF_AND_POS =>
    let cnf := pf.getArguments[0]!
    let i : Nat := pf.getArguments[1]!.getIntegerValue.toNat
    let mut ps : Q(List Prop) := q([])
    let n := cnf.getNumChildren
    for i in [:n] do
      let p : Q(Prop) ← rconsTerm cnf[n - i - 1]!
      ps := q($p :: $ps)
    addThm (← rconsTerm pf.getResult) q(Prop.cnfAndPos $ps $i)
  | .CNF_AND_NEG =>
    let cnf := pf.getArguments[0]!
    let mut ps : Q(List Prop) := q([])
    let n := cnf.getNumChildren
    for i in [:n] do
      let p : Q(Prop) ← rconsTerm cnf[n - i - 1]!
      ps := q($p :: $ps)
    addThm (← rconsTerm pf.getResult) q(Prop.cnfAndNeg $ps)
  | .CNF_OR_POS =>
    let cnf := pf.getArguments[0]!
    let mut ps : Q(List Prop) := q([])
    let n := cnf.getNumChildren
    for i in [:n] do
      let p : Q(Prop) ← rconsTerm cnf[n - i - 1]!
      ps := q($p :: $ps)
    addThm (← rconsTerm pf.getResult) q(Prop.cnfOrPos $ps)
  | .CNF_OR_NEG =>
    let cnf := pf.getArguments[0]!
    let i : Nat := pf.getArguments[1]!.getIntegerValue.toNat
    let mut ps : Q(List Prop) := q([])
    let n := cnf.getNumChildren
    for i in [:n] do
      let p : Q(Prop) ← rconsTerm cnf[n - i - 1]!
      ps := q($p :: $ps)
    addThm (← rconsTerm pf.getResult) q(Prop.cnfOrNeg $ps $i)
  | .CNF_IMPLIES_POS =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    addThm q(¬($p → $q) ∨ ¬$p ∨ $q) q(@Prop.cnfImpliesPos $p $q)
  | .CNF_IMPLIES_NEG1 =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    addThm q(($p → $q) ∨ $p) q(@Prop.cnfImpliesNeg1 $p $q)
  | .CNF_IMPLIES_NEG2 =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    addThm q(($p → $q) ∨ ¬$q) q(@Prop.cnfImpliesNeg2 $p $q)
  | .CNF_EQUIV_POS1 =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    addThm q($p ≠ $q ∨ ¬$p ∨ $q) q(@Prop.cnfEquivPos1 $p $q)
  | .CNF_EQUIV_POS2 =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    addThm q($p ≠ $q ∨ $p ∨ ¬$q) q(@Prop.cnfEquivPos2 $p $q)
  | .CNF_EQUIV_NEG1 =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    addThm q($p = $q ∨ $p ∨ $q) q(@Prop.cnfEquivNeg1 $p $q)
  | .CNF_EQUIV_NEG2 =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    addThm q($p = $q ∨ ¬$p ∨ ¬$q) q(@Prop.cnfEquivNeg2 $p $q)
  | .CNF_XOR_POS1 =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    addThm q(¬XOr $p $q ∨ $p ∨ $q) q(@Prop.cnfXorPos1 $p $q)
  | .CNF_XOR_POS2 =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    addThm q(¬XOr $p $q ∨ ¬$p ∨ ¬$q) q(@Prop.cnfXorPos2 $p $q)
  | .CNF_XOR_NEG1 =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    addThm q(XOr $p $q ∨ ¬$p ∨ $q) q(@Prop.cnfXorNeg1 $p $q)
  | .CNF_XOR_NEG2 =>
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    addThm q(XOr $p $q ∨ $p ∨ ¬$q) q(@Prop.cnfXorNeg2 $p $q)
  | .CNF_ITE_POS1 =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![2]!
    addThm q(¬(ite $c $p $q) ∨ ¬$c ∨ $p) q(@Prop.cnfItePos1 $c $p $q $h)
  | .CNF_ITE_POS2 =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![2]!
    addThm q(¬(ite $c $p $q) ∨ $c ∨ $q) q(@Prop.cnfItePos2 $c $p $q $h)
  | .CNF_ITE_POS3 =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![2]!
    addThm q(¬(ite $c $p $q) ∨ $p ∨ $q) q(@Prop.cnfItePos3 $c $p $q $h)
  | .CNF_ITE_NEG1 =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![2]!
    addThm q(ite $c $p $q ∨ ¬$c ∨ ¬$p) q(@Prop.cnfIteNeg1 $c $p $q $h)
  | .CNF_ITE_NEG2 =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![2]!
    addThm q(ite $c $p $q ∨ $c ∨ ¬$q) q(@Prop.cnfIteNeg2 $c $p $q $h)
  | .CNF_ITE_NEG3 =>
    let c : Q(Prop) ← rconsTerm pf.getArguments[0]![0]!
    let h : Q(Decidable $c) ← Meta.synthInstance q(Decidable $c)
    let p : Q(Prop) ← rconsTerm pf.getArguments[0]![1]!
    let q : Q(Prop) ← rconsTerm pf.getArguments[0]![2]!
    addThm q(ite $c $p $q ∨ ¬$p ∨ ¬$q) q(@Prop.cnfIteNeg3 $c $p $q $h)
  | .REFL =>
    let α : Q(Type) ← rconsSort pf.getArguments[0]!.getSort
    let a : Q($α) ← rconsTerm pf.getArguments[0]!
    addThm q($a = $a) q(Eq.refl $a)
  | .SYMM =>
    let α : Q(Type) ← rconsSort pf.getResult[0]!.getSort
    let a : Q($α) ← rconsTerm pf.getResult[1]!
    let b : Q($α) ← rconsTerm pf.getResult[0]!
    if pf.getResult.getKind == .EQUAL then
      let h : Q($a = $b) ← rconsProof pf.getChildren[0]!
      addThm q($b = $a) q(Eq.symm $h)
    else
      let h : Q($a ≠ $b) ← rconsProof pf.getChildren[0]!
      addThm q($b ≠ $a) q(Ne.symm $h)
  | .TRANS =>
    let cpfs := pf.getChildren
    let α : Q(Type) ← rconsSort cpfs[0]!.getResult[0]!.getSort
    let a : Q($α) ← rconsTerm cpfs[0]!.getResult[0]!
    let mut curr ← rconsProof cpfs[0]!
    for i in [1:cpfs.size] do
      let b : Q($α) ← rconsTerm cpfs[i]!.getResult[0]!
      let c : Q($α) ← rconsTerm cpfs[i]!.getResult[1]!
      let hab : Q($a = $b) := curr
      let hbc : Q($b = $c) ← rconsProof cpfs[i]!
      curr ← addThm q($a = $c) q(Eq.trans $hab $hbc)
    return curr
  | .CONG =>
    let k := pf.getResult[0]!.getKind
    -- This rule needs more care for closures.
    if k == .FORALL then
      rconsForallCong pf rconsProof
    else if k == .EXISTS || k == .WITNESS || k == .LAMBDA || k == .SET_COMPREHENSION then
      let type ← rconsTerm pf.getResult
      addTrust type pf
    else
      let mut assums ← pf.getChildren.mapM rconsProof
      addTac (← rconsTerm pf.getResult) (.cong assums)
  | .NARY_CONG =>
    let mut assums ← pf.getChildren.mapM rconsProof
    addTac (← rconsTerm pf.getResult) (.cong assums)
  | .TRUE_INTRO =>
    let p : Q(Prop) ← rconsTerm pf.getResult[0]!
    let hp : Q($p) ← rconsProof pf.getChildren[0]!
    addThm q($p = True) q(Prop.trueIntro $hp)
  | .TRUE_ELIM =>
    let p : Q(Prop) ← rconsTerm pf.getResult
    let hp : Q($p = True) ← rconsProof pf.getChildren[0]!
    addThm q($p) q(Prop.trueElim $hp)
  | .FALSE_INTRO =>
    let p : Q(Prop) ← rconsTerm pf.getResult[0]!
    let hnp : Q(¬$p) ← rconsProof pf.getChildren[0]!
    addThm q($p = False) q(Prop.falseIntro $hnp)
  | .FALSE_ELIM =>
    let p : Q(Prop) ← rconsTerm pf.getResult[0]!
    let hnp : Q($p = False) ← rconsProof pf.getChildren[0]!
    addThm q(¬$p) q(Prop.falseElim $hnp)
  | .BETA_REDUCE =>
    let α : Q(Type) ← rconsSort pf.getResult[0]!.getSort
    let t  : Q($α) ← rconsTerm pf.getResult[0]!
    let t' : Q($α) ← rconsTerm pf.getResult[1]!
    addThm q($t = $t') q(Eq.refl $t)
  | .BV_BITBLAST_STEP =>
    rconsBB pf
  | .SKOLEM_INTRO =>
    let α : Q(Type) ← rconsSort pf.getResult[0]!.getSort
    let k : Q($α) ← rconsTerm pf.getResult[0]!
    let t : Q($α) ← rconsTerm pf.getResult[1]!
    addThm q($k = $t) q(Eq.refl $t)
  | .SKOLEMIZE =>
    rconsSkolemize pf rconsProof
  | .INSTANTIATE =>
    let xsF  : Q(Prop) ← rconsProof pf.getChildren[0]!
    let mut es := #[]
    for t in pf.getArguments[0]! do
      es := es.push (← rconsTerm t)
    addThm (← rconsTerm pf.getResult) (mkAppN xsF es)
  | .ALPHA_EQUIV =>
    let α : Q(Type) ← rconsSort pf.getResult[0]!.getSort
    let t  : Q($α) ← rconsTerm pf.getResult[0]!
    let t' : Q($α) ← rconsTerm pf.getResult[1]!
    addThm q($t = $t') q(Eq.refl $t)
  | _ =>
    _ ← pf.getChildren.mapM rconsProof
    let type ← rconsTerm pf.getResult
    addTrust type pf
  cacheProof pf e.fvarId!.name
  return e

end Rcons

partial def rconsProof (mv : MVarId) (pf : cvc5.Proof) : MetaM (FVarId × MVarId × List MVarId) := do
  let p : Q(Prop) ← rconsTerm (pf.getResult)
  let Prod.mk (h : Q(True → $p)) (.mk _ _ _ _ _ mv _ mvs)  ← StateT.run (Rcons.rconsProof pf) ⟨{}, {}, 0, #[], mv, mv, #[], #[]⟩
  let ⟨fv, mv, _⟩ ← mv.replace h.fvarId! q($h trivial) q($p)
  return (fv, mv, mvs.toList)

open cvc5 in
def prove (query : String) (timeout : Option Nat) : Lean.MetaM (Except SolverError cvc5.Proof) := Solver.run do
  if let .some timeout := timeout then
    Solver.setOption "tlimit" (toString (1000*timeout))
  Solver.setOption "dag-thresh" "0"
  Solver.setOption "simplification" "none"
  Solver.setOption "enum-inst" "true"
  Solver.setOption "produce-models" "true"
  Solver.setOption "produce-proofs" "true"
  Solver.setOption "proof-elim-subtypes" "true"
  Solver.setOption "proof-granularity" "dsl-rewrite"
  Solver.parse query
  let r ← Solver.checkSat
  if r.isUnsat then
    let ps ← Solver.getProof
    if h : 0 < ps.size then
      trace[smt.debug.reconstruct] (← Solver.proofToString ps[0])
      return ps[0]
  throw (self := instMonadExcept _ _) (SolverError.user_error "something went wrong")

syntax (name := reconstruct) "reconstruct" str : tactic

open Lean.Elab Tactic in
@[tactic reconstruct] def evalReconstruct : Tactic := fun stx =>
  withMainContext do
    let some query := stx[1].isStrLit? | throwError "expected string"
    let r ← prove query none
    match r with
      | .error e => logInfo (repr e)
      | .ok pf =>
        let (_, mv, mvs) ← rconsProof (← getMainGoal) pf
        replaceMainGoal (mv :: mvs)

end Smt.Reconstruct
