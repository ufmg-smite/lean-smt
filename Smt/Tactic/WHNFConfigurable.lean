/-
Copyright (c) 2019-2022 by Microsoft Corporation and the authors listed in the file AUTHORS
and their institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Wojciech Nawrocki
-/
import Lean.Meta.WHNF
import Lean.Meta.CtorRecognizer
import Smt.Tactic.WHNFConfigurableRef

namespace Lean.Meta

/-- Use a fresh name if this one is already in the local context. While Lean seems to handle
shadowing correctly, external tools don't always do so. -/
def bumpNameIfUsed (nm : Name) : MetaM Name :=
  return (← getLCtx).getUnusedName nm

partial def letTelescopeAbstractingAux (fvars : Array Expr) (abs : Expr → MetaM Expr)
    (k : Array Expr → Expr → (Expr → MetaM Expr) → MetaM α)
    : Expr → MetaM α
  | Expr.letE nm t v b nonDep => do
    let nm ← bumpNameIfUsed nm
    withLocalDeclD nm t fun x =>
      letTelescopeAbstractingAux
        (fvars.push x)
        (fun e' => abs (Expr.letE nm t v (e'.abstract #[x]) nonDep))
        k
        (b.instantiate1 x)
  | Expr.mdata md e@(Expr.letE ..) =>
    letTelescopeAbstractingAux fvars (fun e' => abs (Expr.mdata md e')) k e
  | e => k fvars e abs

@[inline] def map3MetaM [MonadControlT MetaM m] [Monad m]
    (f : forall {α}, (β → γ → δ → MetaM α) → MetaM α)
    {α} (k : β → γ → δ → m α)
    : m α :=
  controlAt MetaM fun runInBase => f fun b c d => runInBase <| k b c d

/-- Like `lambdaTelescope` but just for `let` bindings, and the continuation is given an abstraction
function which it can use to reintroduce all the surrounding `let` bindings. The `let` bindings are
defined as `cdecl`s, i.e. their values are not exposed in the local context.

Unlike `lambdaTelescope` followed by `mkLetFVars`, this preserves `mdata` stored on `let` bindings. -/
def letTelescopeAbstracting [MonadControlT MetaM n] [Monad n] {α : Type} (e : Expr)
    (k : Array Expr → Expr → (Expr → MetaM Expr) → n α) : n α :=
  map3MetaM (fun k => letTelescopeAbstractingAux #[] pure k e) k

end Lean.Meta

namespace Smt

open Lean Meta

/- ===========================
   Smart unfolding support
   =========================== -/

def smartUnfoldingSuffix := "_sunfold"

@[inline] def mkSmartUnfoldingNameFor (declName : Name) : Name :=
  Name.mkStr declName smartUnfoldingSuffix

def hasSmartUnfoldingDecl (env : Environment) (declName : Name) : Bool :=
  env.contains (mkSmartUnfoldingNameFor declName)

/-- Add auxiliary annotation to indicate the `match`-expression `e` must be reduced when performing smart unfolding. -/
def markSmartUnfoldingMatch (e : Expr) : Expr :=
  mkAnnotation `sunfoldMatch e

def smartUnfoldingMatch? (e : Expr) : Option Expr :=
  annotation? `sunfoldMatch e

/-- Add auxiliary annotation to indicate expression `e` (a `match` alternative rhs) was successfully reduced by smart unfolding. -/
def markSmartUnfoldingMatchAlt (e : Expr) : Expr :=
  mkAnnotation `sunfoldMatchAlt e

def smartUnfoldingMatchAlt? (e : Expr) : Option Expr :=
  annotation? `sunfoldMatchAlt e

/- ===========================
   Helper methods
   =========================== -/
def isAuxDef (constName : Name) : MetaM Bool := do
  let env ← getEnv
  return isAuxRecursor env constName || isNoConfusion env constName

@[inline] private def matchConstAux {α} (e : Expr) (failK : Unit → ReductionM α) (k : ConstantInfo → List Level → ReductionM α) : ReductionM α :=
  match e with
  | Expr.const name lvls => do
    let (some cinfo) ← getUnfoldableConst? name | failK ()
    k cinfo lvls
  | _ => failK ()

/- ===========================
   Helper functions for reducing recursors
   =========================== -/

private def getFirstCtor (d : Name) : MetaM (Option Name) := do
  let some (ConstantInfo.inductInfo { ctors := ctor::_, ..}) ← getUnfoldableConstNoEx? d | pure none
  return some ctor

private def mkNullaryCtor (type : Expr) (nparams : Nat) : MetaM (Option Expr) := do
  match type.getAppFn with
  | Expr.const d lvls =>
    let (some ctor) ← getFirstCtor d | pure none
    return mkAppN (mkConst ctor lvls) (type.getAppArgs.shrink nparams)
  | _ =>
    return none

def toCtorIfLit : Expr → Expr
  | Expr.lit (Literal.natVal v) =>
    if v == 0 then mkConst `Nat.zero
    else mkApp (mkConst `Nat.succ) (mkRawNatLit (v-1))
  | Expr.lit (Literal.strVal v) =>
    mkApp (mkConst `String.mk) (toExpr v.toList)
  | e => e

private def getRecRuleFor (recVal : RecursorVal) (major : Expr) : Option RecursorRule :=
  match major.getAppFn with
  | Expr.const fn _ => recVal.rules.find? fun r => r.ctor == fn
  | _               => none

private def toCtorWhenK (recVal : RecursorVal) (major : Expr) : ReductionM Expr := do
  let majorType ← inferType major
  let majorType ← instantiateMVars (← whnf majorType)
  let majorTypeI := majorType.getAppFn
  if !majorTypeI.isConstOf recVal.getInduct then
    return major
  else if majorType.hasExprMVar && majorType.getAppArgs[recVal.numParams:].any Expr.hasExprMVar then
    return major
  else do
    let (some newCtorApp) ← mkNullaryCtor majorType recVal.numParams | pure major
    let newType ← inferType newCtorApp
    /- TODO: check whether changing reducibility to default hurts performance here.
       We do that to make sure auxiliary `Eq.rec` introduced by the `match`-compiler
       are reduced even when `TransparencyMode.reducible` (like in `simp`).

       We use `withNewMCtxDepth` to make sure metavariables at `majorType` are not assigned.
       For example, given `major : Eq ?x y`, we don't want to apply K by assigning `?x := y`.
    -/
    if (← withAtLeastTransparency TransparencyMode.default <| withNewMCtxDepth <| isDefEq majorType newType) then
      return newCtorApp
    else
      return major

/--
  Create the `i`th projection `major`. It tries to use the auto-generated projection functions if available. Otherwise falls back
  to `Expr.proj`.
-/
def mkProjFn (ctorVal : ConstructorVal) (us : List Level) (params : Array Expr) (i : Nat) (major : Expr) : CoreM Expr := do
  match getStructureInfo? (← getEnv) ctorVal.induct with
  | none => return mkProj ctorVal.induct i major
  | some info => match info.getProjFn? i with
    | none => return mkProj ctorVal.induct i major
    | some projFn => return mkApp (mkAppN (mkConst projFn us) params) major

/--
  If `major` is not a constructor application, and its type is a structure `C ...`, then return `C.mk major.1 ... major.n`

  \pre `inductName` is `C`.

  If `Meta.Config.etaStruct` is `false` or the condition above does not hold, this method just returns `major`. -/
private def toCtorWhenStructure (inductName : Name) (major : Expr) : ReductionM Expr := do
  unless (← useEtaStruct inductName) do
    return major
  let env ← getEnv
  if !isStructureLike env inductName then
    return major
  else if let some _ ← isConstructorApp? major then
    return major
  else
    let majorType ← inferType major
    let majorType ← instantiateMVars (← whnf majorType)
    let majorTypeI := majorType.getAppFn
    if !majorTypeI.isConstOf inductName then
      return major
    match majorType.getAppFn with
    | Expr.const d us =>
      if (← whnfD (← inferType majorType)) == mkSort levelZero then
        return major -- We do not perform eta for propositions, see implementation in the kernel
      else
        let some ctorName ← getFirstCtor d | pure major
        let ctorInfo ← getConstInfoCtor ctorName
        let params := majorType.getAppArgs.shrink ctorInfo.numParams
        let mut result := mkAppN (mkConst ctorName us) params
        for i in [:ctorInfo.numFields] do
          result := mkApp result (← mkProjFn ctorInfo us params i major)
        return result
    | _ => return major

/-- Auxiliary function for reducing recursor applications. -/
private def reduceRec (recVal : RecursorVal) (recLvls : List Level) (recArgs : Array Expr)
    (failK : Unit → ReductionM α) (successK : Expr → ReductionM α)
    : ReductionM α := do
  let majorIdx := recVal.getMajorIdx
  trace[Smt.reduce.rec] "{recVal.name} with args (#{majorIdx} major){indentD recArgs}"
  if h : majorIdx < recArgs.size then
    let cont (major : Expr) : ReductionM (Option Expr) := do
      let mut major := major
      if recVal.k then
        major ← toCtorWhenK recVal major
      major := toCtorIfLit major
      major ← toCtorWhenStructure recVal.getInduct major
      let some rule := getRecRuleFor recVal major | return none
      let majorArgs := major.getAppArgs
      guard (recLvls.length == recVal.levelParams.length)
      let rhs := rule.rhs.instantiateLevelParams recVal.levelParams recLvls
      -- Apply parameters, motives and minor premises from recursor application.
      let rhs := mkAppRange rhs 0 (recVal.numParams+recVal.numMotives+recVal.numMinors) recArgs
      /- The number of parameters in the constructor is not necessarily
        equal to the number of parameters in the recursor when we have
        nested inductive types. -/
      let nparams := majorArgs.size - rule.nfields
      let rhs := mkAppRange rhs nparams majorArgs.size majorArgs
      let rhs := mkAppRange rhs (majorIdx + 1) recArgs.size recArgs
      return rhs

    let cont' : Option Expr → ReductionM α
      | some res => do
        trace[Smt.reduce.rec] "⤳ {res}"
        successK res
      | none => do
        trace[Smt.reduce.rec] "failed."
        failK ()

    let major ← whnf <| recArgs.get ⟨majorIdx, h⟩
    if (← read).letPushElim then
      letTelescopeAbstracting major fun _ major abs => do
        let e' ← cont major
        let e' ← e'.mapM fun e => abs e
        cont' e'
    else
      cont' (← cont major)
  else
    failK ()

/- ===========================
   Helper functions for reducing Quot.lift and Quot.ind
   =========================== -/

/-- Auxiliary function for reducing `Quot.lift` and `Quot.ind` applications. -/
private def reduceQuotRec (recVal  : QuotVal) (_ : List Level) (recArgs : Array Expr)
    (failK : Unit → ReductionM α) (successK : Expr → ReductionM α)
    : ReductionM α :=
  let process (majorPos argPos : Nat) : ReductionM α :=
    if h : majorPos < recArgs.size then do
      let major := recArgs.get ⟨majorPos, h⟩
      let major ← whnf major
      match major with
      | Expr.app (Expr.app (Expr.app (Expr.const majorFn _) _) _) majorArg => do
        let some (ConstantInfo.quotInfo { kind := QuotKind.ctor, .. }) ← getUnfoldableConstNoEx? majorFn | failK ()
        let f := recArgs[argPos]!
        let r := mkApp f majorArg
        let recArity := majorPos + 1
        successK <| mkAppRange r recArity recArgs.size recArgs
      | _ => failK ()
    else
      failK ()
  match recVal.kind with
  | QuotKind.lift => process 5 3
  | QuotKind.ind  => process 4 3
  | _             => failK ()

/- ===========================
   Helper function for extracting "stuck term"
   =========================== -/

mutual
  private partial def isRecStuck? (recVal : RecursorVal) (recArgs : Array Expr) : ReductionM (Option MVarId) :=
    if recVal.k then
      -- TODO: improve this case
      return none
    else do
      let majorIdx := recVal.getMajorIdx
      if h : majorIdx < recArgs.size then do
        let major := recArgs.get ⟨majorIdx, h⟩
        let major ← whnf major
        getStuckMVar? major
      else
        return none

  private partial def isQuotRecStuck? (recVal : QuotVal) (recArgs : Array Expr) : ReductionM (Option MVarId) :=
    let process? (majorPos : Nat) : ReductionM (Option MVarId) :=
      if h : majorPos < recArgs.size then do
        let major := recArgs.get ⟨majorPos, h⟩
        let major ← whnf major
        getStuckMVar? major
      else
        return none
    match recVal.kind with
    | QuotKind.lift => process? 5
    | QuotKind.ind  => process? 4
    | _             => return none

  /-- Return `some (Expr.mvar mvarId)` if metavariable `mvarId` is blocking reduction. -/
  partial def getStuckMVar? (e : Expr) : ReductionM (Option MVarId) := do
    match e with
    | Expr.mdata _ e  => getStuckMVar? e
    | Expr.proj _ _ e => getStuckMVar? (← whnf e)
    | Expr.mvar .. => do
      let e ← instantiateMVars e
      match e with
      | Expr.mvar mvarId => pure (some mvarId)
      | _ => getStuckMVar? e
    | Expr.app f .. =>
      let f := f.getAppFn
      match f with
      | Expr.mvar mvarId   => return some mvarId
      | Expr.const fName _ =>
        let cinfo? ← getUnfoldableConstNoEx? fName
        match cinfo? with
        | some $ ConstantInfo.recInfo recVal  => isRecStuck? recVal e.getAppArgs
        | some $ ConstantInfo.quotInfo recVal => isQuotRecStuck? recVal e.getAppArgs
        | _                                => return none
      | Expr.proj _ _ e => getStuckMVar? (← whnf e)
      | _ => return none
    | _ => return none
end

/- ===========================
   Weak Head Normal Form auxiliary combinators
   =========================== -/

/-- Auxiliary combinator for handling easy WHNF cases. It takes a function for handling the "hard" cases as an argument -/
@[specialize] partial def whnfEasyCases (e : Expr) (k : Expr → ReductionM Expr) : ReductionM Expr := do
  match e with
  | Expr.forallE ..    => return e
  | Expr.lam ..        => return e
  | Expr.sort ..       => return e
  | Expr.lit ..        => return e
  | Expr.bvar ..       => unreachable!
  | Expr.letE ..       => k e
  | Expr.const ..      => k e
  | Expr.app ..        => k e
  | Expr.proj ..       => k e
  | Expr.mdata ..      => k e
  | Expr.fvar fvarId   =>
    let decl ← fvarId.getDecl
    match decl with
    | LocalDecl.cdecl .. => return e
    | LocalDecl.ldecl (value := v) .. =>
      let cfg ← getConfig
      if cfg.trackZetaDelta then
        modify fun s => { s with zetaDeltaFVarIds := s.zetaDeltaFVarIds.insert fvarId }
      whnfEasyCases v k
  | Expr.mvar mvarId   =>
    match (← getExprMVarAssignment? mvarId) with
    | some v => whnfEasyCases v k
    | none   => return e

@[specialize] private def deltaDefinition (c : ConstantInfo) (lvls : List Level)
    (failK : Unit → MetaM α) (successK : Expr → MetaM α) : MetaM α := do
  if c.levelParams.length != lvls.length then
    failK ()
  else
    successK (← instantiateValueLevelParams c lvls)

@[specialize] private def deltaBetaDefinition (c : ConstantInfo) (lvls : List Level) (revArgs : Array Expr)
    (failK : Unit → ReductionM α) (successK : Expr → ReductionM α) (preserveMData := false) : ReductionM α := do
  if c.levelParams.length != lvls.length then
    failK ()
  else
    let val ← instantiateValueLevelParams c lvls
    let val := val.betaRev revArgs (preserveMData := preserveMData)
    successK val

inductive ReduceMatcherResult where
  | reduced (val : Expr)
  | stuck   (val : Expr)
  | notMatcher
  | partialApp

/--
  The "match" compiler uses `if-then-else` expressions and other auxiliary declarations to compile match-expressions such as
  ```
  match v with
  | 'a' => 1
  | 'b' => 2
  | _   => 3
  ```
  because it is more efficient than using `casesOn` recursors.
  The method `reduceMatcher?` fails if these auxiliary definitions (e.g., `ite`) cannot be unfolded in the current
  transparency setting. This is problematic because tactics such as `simp` use `TransparencyMode.reducible`, and
  most users assume that expressions such as
  ```
  match 0 with
  | 0 => 1
  | 100 => 2
  | _ => 3
  ```
  should reduce in any transparency mode.
  Thus, we define a custom `canUnfoldAtMatcher` predicate for `whnfMatcher`.

  This solution is not very modular because modications at the `match` compiler require changes here.
  We claim this is defensible because it is reducing the auxiliary declaration defined by the `match` compiler.

  Alternative solution: tactics that use `TransparencyMode.reducible` should rely on the equations we generated for match-expressions.
  This solution is also not perfect because the match-expression above will not reduce during type checking when we are not using
  `TransparencyMode.default` or `TransparencyMode.all`.
-/
def canUnfoldAtMatcher
    (prevUnfoldAt? : Option (Meta.Config → ConstantInfo → CoreM Bool))
    (cfg : Meta.Config) (info : ConstantInfo) : CoreM Bool := do
  if let some prevUnfoldAt := prevUnfoldAt? then
    prevUnfoldAt cfg info
  else match cfg.transparency with
  | TransparencyMode.all     => return true
  | TransparencyMode.default => return true
  | _ =>
    if (← isReducible info.name) || isGlobalInstance (← getEnv) info.name then
      return true
    else if hasMatchPatternAttribute (← getEnv) info.name then
      return true
    else
      return info.name == ``ite
       || info.name == ``dite
       || info.name == ``decEq
       || info.name == ``Nat.decEq
       || info.name == ``Char.ofNat   || info.name == ``Char.ofNatAux
       || info.name == ``String.decEq || info.name == ``List.hasDecEq
       || info.name == ``Fin.ofNat
       || info.name == ``UInt8.ofNat  || info.name == ``UInt8.decEq
       || info.name == ``UInt16.ofNat || info.name == ``UInt16.decEq
       || info.name == ``UInt32.ofNat || info.name == ``UInt32.decEq
       || info.name == ``UInt64.ofNat || info.name == ``UInt64.decEq
       /- Remark: we need to unfold the following two definitions because they are used for `Fin`, and
          lazy unfolding at `isDefEq` does not unfold projections.  -/
       || info.name == ``HMod.hMod || info.name == ``Mod.mod

private def whnfMatcher (e : Expr) : ReductionM Expr := do
  /- When reducing `match` expressions, if the reducibility setting is at `TransparencyMode.reducible`,
     we increase it to `TransparencyMode.instance`. We use the `TransparencyMode.reducible` in many places (e.g., `simp`),
     and this setting prevents us from reducing `match` expressions where the discriminants are terms such as `OfNat.ofNat α n inst`.
     For example, `simp [Int.div]` will not unfold the application `Int.div 2 1` occuring in the target.

     TODO: consider other solutions; investigate whether the solution above produces counterintuitive behavior.  -/
  let mut transparency ← getTransparency
  if transparency == TransparencyMode.reducible then
    transparency := TransparencyMode.instances
  withTransparency transparency <|
    withTheReader Meta.Context (fun ctx => { ctx with canUnfold? := canUnfoldAtMatcher ctx.canUnfold? }) do
      whnf e

def reduceMatcher? (e : Expr) : ReductionM ReduceMatcherResult := do
  trace[Smt.reduce.matcher] "{e}"
  match e.getAppFn with
  | Expr.const declName declLevels =>
    let some info ← getMatcherInfo? declName
      | do
        trace[Smt.reduce.matcher] "not a matcher."
        return ReduceMatcherResult.notMatcher
    let args := e.getAppArgs
    let prefixSz := info.numParams + 1 + info.numDiscrs
    if args.size < prefixSz + info.numAlts then
      trace[Smt.reduce.matcher] "partial app."
      return ReduceMatcherResult.partialApp
    else
      let constInfo ← getConstInfo declName
      let f ← instantiateValueLevelParams constInfo declLevels
      let auxApp := mkAppN f args[0:prefixSz]
      let auxAppType ← inferType auxApp
      forallBoundedTelescope auxAppType info.numAlts fun hs _ => do
        let auxApp ← whnfMatcher (mkAppN auxApp hs)

        let cont (auxApp : Expr) : ReductionM ReduceMatcherResult := do
          let auxAppFn := auxApp.getAppFn
          let mut i := prefixSz
          for h in hs do
            if auxAppFn == h then
              let result := mkAppN args[i]! auxApp.getAppArgs
              let result := mkAppN result args[prefixSz + info.numAlts:args.size]
              let res := result.headBeta
              trace[Smt.reduce.matcher] "⤳ {res}"
              return ReduceMatcherResult.reduced res
            i := i + 1
          trace[Smt.reduce.matcher] "stuck at {auxApp}"
          return ReduceMatcherResult.stuck auxApp

        if (← read).letPushElim then
          letTelescopeAbstracting auxApp fun _ auxApp abs => do
            match ← cont auxApp with
            | .reduced e => return .reduced (← abs e)
            | .stuck e   => return .stuck (← abs e)
            | res        => return res
        else cont auxApp
  | _ => do
    trace[Smt.reduce.matcher] "not a matcher."
    return ReduceMatcherResult.notMatcher

private def projectCore? (e : Expr) (i : Nat) : MetaM (Option Expr) := do
  let e := toCtorIfLit e
  matchConstCtor e.getAppFn (fun _ => pure none) fun ctorVal _ =>
    let numArgs := e.getAppNumArgs
    let idx := ctorVal.numParams + i
    if idx < numArgs then
      return some (e.getArg! idx)
    else
      return none

def project? (e : Expr) (i : Nat) : ReductionM (Option Expr) := do
  projectCore? (← whnf e) i

/-- Reduce kernel projection `Expr.proj ..` expression. -/
def reduceProj? (e : Expr) : ReductionM (Option Expr) := do
  match e with
  | Expr.proj _ i c => project? c i
  | _               => return none

/--
  Auxiliary method for reducing terms of the form `?m t_1 ... t_n` where `?m` is delayed assigned.
  Recall that we can only expand a delayed assignment when all holes/metavariables in the assigned value have been "filled".
-/
private def whnfDelayedAssigned? (f' : Expr) (e : Expr) : MetaM (Option Expr) := do
  if f'.isMVar then
    match (← getDelayedMVarAssignment? f'.mvarId!) with
    | none => return none
    | some { fvars, mvarIdPending } =>
      let args := e.getAppArgs
      if fvars.size > args.size then
        -- Insufficient number of argument to expand delayed assignment
        return none
      else
        let newVal ← instantiateMVars (mkMVar mvarIdPending)
        if newVal.hasExprMVar then
           -- Delayed assignment still contains metavariables
           return none
        else
           let newVal := newVal.abstract fvars
           let result := newVal.instantiateRevRange 0 fvars.size args
           return mkAppRange result fvars.size args.size args
  else
    return none

def traceReduce [Monad m] (e : Expr) (e' : Except ε Expr) : m MessageData :=
  return m!"{e} ⤳ " ++ match e' with
    | .ok e'   => m!"{e'}"
    | .error _ => m!"{bombEmoji}"

/--
  Apply beta-reduction, zeta-reduction (i.e., unfold let local-decls), iota-reduction,
  expand let-expressions, expand assigned meta-variables.

  The parameter `deltaAtProj` controls how to reduce projections `s.i`. If `deltaAtProj == true`,
  then delta reduction is used to reduce `s` (i.e., `whnf` is used), otherwise `whnfCore`.
  We only set this flag to `false` when implementing `isDefEq`.
-/
partial def whnfCore (e : Expr) (deltaAtProj : Bool := true) : ReductionM Expr :=
  go e
where
  go (e : Expr) : ReductionM Expr := withTraceNode `Smt.reduce.whnfCore (traceReduce e ·) <| do
    whnfEasyCases e fun e => do
      match e with
      | Expr.const ..  => pure e
      | Expr.letE _ _ v b _ => do
        -- NOTE(WN): Should core Lean do a `zetaNonDep` check here?
        if (← readThe Smt.Config).zeta then go <| b.instantiate1 v
        else return e
      | Expr.app f ..       =>
        let f := f.getAppFn
        let f ← go f
        -- NOTE(WN): We make a significant change to the evaluation order by not only WHNFing
        -- arguments eagerly, CBV-style, but also doing so with the full procedure rather than
        -- just `whnfCore` (so that a lack of delta-unfolding does not block let-lifting).
        let revArgs ← e.getAppRevArgs.mapM whnf

        let mut k (f : Expr) (revArgs : Array Expr) : ReductionM Expr := do
          let e := mkAppRev f revArgs
          if f.isLambda then
            go <| f.betaRev revArgs
          else if let some eNew ← whnfDelayedAssigned? f e then
            go eNew
          else
            -- Is this just an optimization?
            -- let e := if f == f' then e else e.updateFn f'
            match (← reduceMatcher? e) with
            | ReduceMatcherResult.reduced eNew => go eNew
            | ReduceMatcherResult.partialApp   => pure e
            | ReduceMatcherResult.stuck _      => pure e
            | ReduceMatcherResult.notMatcher   =>
              matchConstAux f (fun _ => return e) fun cinfo lvls =>
                match cinfo with
                | ConstantInfo.recInfo rec    => reduceRec rec lvls revArgs.reverse (fun _ => return e) go
                | ConstantInfo.quotInfo rec   => reduceQuotRec rec lvls revArgs.reverse (fun _ => return e) go
                | c@(ConstantInfo.defnInfo _) => do
                  if (← isAuxDef c.name) then
                    deltaBetaDefinition c lvls revArgs (fun _ => return e) go
                  else
                    return e
                | _ => return e

        if (← read).letPushElim then
          for arg in revArgs.reverse do
            k := fun f acc => do
              letTelescopeAbstracting arg fun _ arg absFn => do
                let res ← k f (acc.push arg)
                absFn res

          letTelescopeAbstracting f fun _ f absFn => do
            let res ← k f #[]
            absFn res
        else
          k f revArgs

      | Expr.proj pNm i c =>
        let c ← if deltaAtProj then whnf c else whnfCore c

        if (← read).letPushElim then
        -- if false then
          letTelescopeAbstracting c fun _ c absFn => do
            match (← projectCore? c i) with
            | some e => absFn e
            | none => absFn (Expr.proj pNm i c)
        else match (← projectCore? c i) with
        | some e => go e
        | none => return e
      | Expr.mdata md (Expr.letE nm t v b nonDep) =>
        let zeta := md.getBool `zeta (← read).zeta
        if zeta then go <| b.instantiate1 v
        else
          let t' ← go t
          let v' ← go v
          let nm ← bumpNameIfUsed nm
          let b' ← withLocalDeclD nm t' fun x => do
            let b' ← go (b.instantiate1 x)
            return b'.abstract #[x]
          return Expr.mdata md (Expr.letE nm t' v' b' nonDep)
      | Expr.mdata _ e => go e
      | _ => unreachable!

/--
  Recall that `_sunfold` auxiliary definitions contains the markers: `markSmartUnfoldingMatch` (*) and `markSmartUnfoldingMatchAlt` (**).
  For example, consider the following definition
  ```
  def r (i j : Nat) : Nat :=
    i +
      match j with
      | Nat.zero => 1
      | Nat.succ j =>
        i + match j with
            | Nat.zero => 2
            | Nat.succ j => r i j
  ```
  produces the following `_sunfold` auxiliary definition with the markers
  ```
  def r._sunfold (i j : Nat) : Nat :=
    i +
      (*) match j with
      | Nat.zero => (**) 1
      | Nat.succ j =>
        i + (*) match j with
            | Nat.zero => (**) 2
            | Nat.succ j => (**) r i j
  ```

  `match` expressions marked with `markSmartUnfoldingMatch` (*) must be reduced, otherwise the resulting term is not definitionally
   equal to the given expression. The recursion may be interrupted as soon as the annotation `markSmartUnfoldingAlt` (**) is reached.

  For example, the term `r i j.succ.succ` reduces to the definitionally equal term `i + i * r i j`
-/
partial def smartUnfoldingReduce? (e : Expr) : ReductionM (Option Expr) := do
  trace[Smt.reduce.smartUnfoldingReduce] "{e}"
  match ← go e |>.run with
  | some e' =>
    trace[Smt.reduce.smartUnfoldingReduce] "⤳ {e'}"
    return some e'
  | none =>
    trace[Smt.reduce.smartUnfoldingReduce] "failed."
    return none

where
  go (e : Expr) : OptionT ReductionM Expr := do
    match e with
    | Expr.letE n t v b _ => withLetDecl n t (← go v) fun x => do mkLetFVars #[x] (← go (b.instantiate1 x))
    | Expr.lam .. => lambdaTelescope e fun xs b => do mkLambdaFVars xs (← go b)
    | Expr.app f a .. => return mkApp (← go f) (← go a)
    | Expr.proj _ _ s => return e.updateProj! (← go s)
    | Expr.mdata _ b  =>
      if let some m := smartUnfoldingMatch? e then
        goMatch m
      else
        return e.updateMData! (← go b)
    | _ => return e

  goMatch (e : Expr) : OptionT ReductionM Expr := do
    match (← reduceMatcher? e) with
    | ReduceMatcherResult.reduced e =>
      if let some alt := smartUnfoldingMatchAlt? e then
        return alt
      else
        go e
    | ReduceMatcherResult.stuck e' =>
      let mvarId ← getStuckMVar? e'
      /- Try to "unstuck" by resolving pending TC problems -/
      if (← Meta.synthPending mvarId) then
        goMatch e
      else
        failure
    | _ => failure

def shouldUnfold (ci : ConstantInfo) : ReductionM Bool := do
  let some canUnfold := (← readThe Meta.Context).canUnfold? | return true
  let cfg := (← readThe Meta.Context).config
  canUnfold cfg ci

mutual

  /--
    Auxiliary method for unfolding a class projection.
  -/
  partial def unfoldProjInst? (e : Expr) : ReductionM (Option Expr) := do
    match e.getAppFn with
    | Expr.const declName .. =>
      match (← getProjectionFnInfo? declName) with
      | some { fromClass := true, .. } =>
        match (← withDefault <| unfoldDefinition? e) with
        | none   => return none
        | some e =>
          match (← withReducibleAndInstances <| reduceProj? e.getAppFn) with
          | none   => return none
          | some r => return mkAppN r e.getAppArgs |>.headBeta
      | _ => return none
    | _ => return none

  /--
    Auxiliary method for unfolding a class projection. when transparency is set to `TransparencyMode.instances`.
    Recall that class instance projections are not marked with `[reducible]` because we want them to be
    in "reducible canonical form".
  -/
  partial def unfoldProjInstWhenIntances? (e : Expr) : ReductionM (Option Expr) := do
    if (← getTransparency) != TransparencyMode.instances then
      return none
    else
      unfoldProjInst? e

  /-- Unfold definition using "smart unfolding" if possible. -/
  partial def unfoldDefinition? (e : Expr) : ReductionM (Option Expr) :=
    match e with
    | Expr.app f _ =>
      matchConstAux f.getAppFn (fun _ => unfoldProjInstWhenIntances? e) fun fInfo fLvls => do
        -- NOTE(WN): this not being checked might be a Lean bug
        unless ← shouldUnfold fInfo do return none
        if fInfo.levelParams.length != fLvls.length then
          return none
        else
          let unfoldDefault (_ : Unit) : ReductionM (Option Expr) :=
            if fInfo.hasValue then
              deltaBetaDefinition fInfo fLvls e.getAppRevArgs (fun _ => pure none) (fun e => pure (some e))
            else
              return none
          if smartUnfolding.get (← getOptions) then
            match ((← getEnv).find? (mkSmartUnfoldingNameFor fInfo.name)) with
            | some fAuxInfo@(ConstantInfo.defnInfo _) =>
              -- We use `preserveMData := true` to make sure the smart unfolding annotation are not erased in an over-application.
              deltaBetaDefinition fAuxInfo fLvls e.getAppRevArgs (preserveMData := true) (fun _ => pure none) fun e₁ => do
                let some r ← smartUnfoldingReduce? e₁ | return none
                /-
                  If `smartUnfoldingReduce?` succeeds, we should still check whether the argument the
                  structural recursion is recursing on reduces to a constructor.
                  This extra check is necessary in definitions (see issue #1081) such as
                  ```
                  inductive Vector (α : Type u) : Nat → Type u where
                    | nil  : Vector α 0
                    | cons : α → Vector α n → Vector α (n+1)

                  def Vector.insert (a: α) (i : Fin (n+1)) (xs : Vector α n) : Vector α (n+1) :=
                    match i, xs with
                    | ⟨0,   _⟩,        xs => cons a xs
                    | ⟨i+1, h⟩, cons x xs => cons x (xs.insert a ⟨i, Nat.lt_of_succ_lt_succ h⟩)
                  ```
                  The structural recursion is being performed using the vector `xs`. That is, we used `Vector.brecOn` to define
                  `Vector.insert`. Thus, an application `xs.insert a ⟨0, h⟩` is **not** definitionally equal to
                  `Vector.cons a xs` because `xs` is not a constructor application (the `Vector.brecOn` application is blocked).

                  Remark 1: performing structural recursion on `Fin (n+1)` is not an option here because it is a `Subtype` and
                  and the repacking in recursive applications confuses the structural recursion module.

                  Remark 2: the match expression reduces reduces to `cons a xs` when the discriminants are `⟨0, h⟩` and `xs`.

                  Remark 3: this check is unnecessary in most cases, but we don't need dependent elimination to trigger the issue
                  fixed by this extra check. Here is another example that triggers the issue fixed by this check.
                  ```
                  def f : Nat → Nat → Nat
                    | 0,   y   => y
                    | x+1, y+1 => f (x-2) y
                    | x+1, 0   => 0

                  theorem ex : f 0 y = y := rfl
                  ```

                  Remark 4: the `return some r` in the following `let` is not a typo. Binport generated .olean files do not
                  store the position of recursive arguments for definitions using structural recursion.
                  Thus, we should keep `return some r` until Mathlib has been ported to Lean 3.
                  Note that the `Vector` example above does not even work in Lean 3.
                -/
                let some recArgPos ← getStructuralRecArgPos? fInfo.name | return some r
                let numArgs := e.getAppNumArgs
                if recArgPos >= numArgs then return none
                let recArg := e.getArg! recArgPos numArgs
                if !(← isConstructorApp (← whnfMatcher recArg)) then return none
                return some r
            | _ =>
              if (← getMatcherInfo? fInfo.name).isSome then
                -- Recall that `whnfCore` tries to reduce "matcher" applications.
                return none
              else
                unfoldDefault ()
          else
            unfoldDefault ()
    | Expr.const declName lvls => do
      if smartUnfolding.get (← getOptions) && (← getEnv).contains (mkSmartUnfoldingNameFor declName) then
        return none
      else
        let (some (cinfo@(ConstantInfo.defnInfo _))) ← getUnfoldableConstNoEx? declName | pure none
        deltaDefinition cinfo lvls
          (fun _ => pure none)
          (fun e => pure (some e))
    | _ => return none
end

def unfoldDefinition (e : Expr) : ReductionM Expr := do
  let some e ← unfoldDefinition? e | throwError "failed to unfold definition{indentExpr e}"
  return e

@[specialize] partial def whnfHeadPred (e : Expr) (pred : Expr → ReductionM Bool) : ReductionM Expr :=
  whnfEasyCases e fun e => do
    let e ← whnfCore e
    if (← pred e) then
        match (← unfoldDefinition? e) with
        | some e => whnfHeadPred e pred
        | none   => return e
    else
      return e

def whnfUntil (e : Expr) (declName : Name) : ReductionM (Option Expr) := do
  let e ← whnfHeadPred e (fun e => return !e.isAppOf declName)
  if e.isAppOf declName then
    return e
  else
    return none

/-- Try to reduce matcher/recursor/quot applications. We say they are all "morally" recursor applications. -/
def reduceRecMatcher? (e : Expr) : ReductionM (Option Expr) := do
  if !e.isApp then
    return none
  else match (← reduceMatcher? e) with
    | ReduceMatcherResult.reduced e => return e
    | _ => matchConstAux e.getAppFn (fun _ => pure none) fun cinfo lvls => do
      match cinfo with
      | ConstantInfo.recInfo «rec»  => reduceRec «rec» lvls e.getAppArgs (fun _ => pure none) (fun e => pure (some e))
      | ConstantInfo.quotInfo «rec» => reduceQuotRec «rec» lvls e.getAppArgs (fun _ => pure none) (fun e => pure (some e))
      | c@(ConstantInfo.defnInfo _) =>
        if (← isAuxDef c.name) then
          deltaBetaDefinition c lvls e.getAppRevArgs (fun _ => pure none) (fun e => pure (some e))
        else
          return none
      | _ => return none

def reduceNative? (e : Expr) : MetaM (Option Expr) :=
  match e with
  | Expr.app (Expr.const fName _) (Expr.const argName _) =>
    if fName == ``Lean.reduceBool then do
      return toExpr (← reduceBoolNative argName)
    else if fName == ``Lean.reduceNat then do
      return toExpr (← reduceNatNative argName)
    else
      return none
  | _ =>
    return none

@[inline] def withNatValue {α} (a : Expr) (k : Nat → ReductionM (Option α)) : ReductionM (Option α) := do
  let a ← whnf a
  match a with
  | Expr.const `Nat.zero _      => k 0
  | Expr.lit (Literal.natVal v) => k v
  | _                           => return none

def reduceUnaryNatOp (f : Nat → Nat) (a : Expr) : ReductionM (Option Expr) :=
  withNatValue a fun a =>
  return mkRawNatLit <| f a

def reduceBinNatOp (f : Nat → Nat → Nat) (a b : Expr) : ReductionM (Option Expr) :=
  withNatValue a fun a =>
  withNatValue b fun b => do
  trace[Meta.isDefEq.whnf.reduceBinOp] "{a} op {b}"
  return mkRawNatLit <| f a b

def reduceBinNatPred (f : Nat → Nat → Bool) (a b : Expr) : ReductionM (Option Expr) := do
  withNatValue a fun a =>
  withNatValue b fun b =>
  return toExpr <| f a b

def reduceNat? (e : Expr) : ReductionM (Option Expr) :=
  if e.hasFVar || e.hasMVar then
    return none
  else match e with
    | Expr.app (Expr.const fn _) a                =>
      if fn == ``Nat.succ then
        reduceUnaryNatOp Nat.succ a
      else
        return none
    | Expr.app (Expr.app (Expr.const fn _) a1) a2 =>
      if fn == ``Nat.add then reduceBinNatOp Nat.add a1 a2
      else if fn == ``Nat.sub then reduceBinNatOp Nat.sub a1 a2
      else if fn == ``Nat.mul then reduceBinNatOp Nat.mul a1 a2
      else if fn == ``Nat.div then reduceBinNatOp Nat.div a1 a2
      else if fn == ``Nat.mod then reduceBinNatOp Nat.mod a1 a2
      else if fn == ``Nat.beq then reduceBinNatPred Nat.beq a1 a2
      else if fn == ``Nat.ble then reduceBinNatPred Nat.ble a1 a2
      else return none
    | _ =>
      return none


@[inline] private def useWHNFCache (_ : Expr) : MetaM Bool := do
  -- Can't straightforwardly use the WHNF cache with configurable rules.
  return false
  -- We cache only closed terms without expr metavars.
  -- Potential refinement: cache if `e` is not stuck at a metavariable
  -- if e.hasFVar || e.hasExprMVar || (← read).canUnfold?.isSome then
  --   return false
  -- else
  --   match (← getConfig).transparency with
  --   | TransparencyMode.default => return true
  --   | TransparencyMode.all     => return true
  --   | _                        => return false

@[inline] private def cached? (useCache : Bool) (e : Expr) : MetaM (Option Expr) := do
  if useCache then
    match (← getConfig).transparency with
    | TransparencyMode.default => return (← get).cache.whnfDefault.find? e
    | TransparencyMode.all     => return (← get).cache.whnfAll.find? e
    | _                        => unreachable!
  else
    return none

private def cache (useCache : Bool) (e r : Expr) : MetaM Expr := do
  if useCache then
    match (← getConfig).transparency with
    | TransparencyMode.default => modify fun s => { s with cache.whnfDefault := s.cache.whnfDefault.insert e r }
    | TransparencyMode.all     => modify fun s => { s with cache.whnfAll     := s.cache.whnfAll.insert e r }
    | _                        => unreachable!
  return r

partial def whnfImp (e : Expr) : ReductionM Expr :=
  withIncRecDepth <| withTraceNode `Smt.reduce.whnf  (traceReduce e ·) <| whnfEasyCases e fun e => do
    Core.checkMaxHeartbeats "Smt.whnf"
    let useCache ← useWHNFCache e
    let e' ← match (← cached? useCache e) with
    | some e' => pure e'
    | none    =>
      let e' ← whnfCore e
      match (← reduceNat? e') with
      | some v => cache useCache e v
      | none   =>
        match (← reduceNative? e') with
        | some v => cache useCache e v
        | none   =>
          match (← unfoldDefinition? e') with
          | some e => whnfImp e
          | none   => cache useCache e e'
    return e'

/-- If `e` is a projection function that satisfies `p`, then reduce it -/
def reduceProjOf? (e : Expr) (p : Name → Bool) : MetaM (Option Expr) := do
  if !e.isApp then
    pure none
  else match e.getAppFn with
    | Expr.const name .. => do
      let env ← getEnv
      match env.getProjectionStructureName? name with
      | some structName =>
        if p structName then
          Meta.unfoldDefinition? e
        else
          pure none
      | none => pure none
    | _ => pure none

namespace MonadCacheT

variable {ω α β : Type} {m : Type → Type} [STWorld ω m] [BEq α] [Hashable α] [MonadLiftT (ST ω) m] [Monad m]

instance (ε) [always : MonadAlwaysExcept ε m] : MonadAlwaysExcept ε (MonadCacheT α β m) where
  except := let _ := always.except; inferInstance

end MonadCacheT

partial def reduce (e : Expr) (explicitOnly skipTypes skipProofs := true) : ReductionM Expr :=
  let rec visit (e : Expr) : MonadCacheT Expr Expr ReductionM Expr :=
    checkCache e fun _ => Core.withIncRecDepth <| withTraceNode `Smt.reduce (traceReduce e ·) do
      if (← (pure skipTypes <&&> isType e)) then
        return e
      else if (← (pure skipProofs <&&> isProof e)) then
        return e
      else
        let e ← whnf e
        let e' ← match e with
        | Expr.app .. =>
          -- This case happens when the application was not substituted by WHNF,
          -- meaning that it must be stuck.
          let f     ← visit e.getAppFn
          let nargs := e.getAppNumArgs
          let finfo ← getFunInfoNArgs f nargs
          let mut args  := e.getAppArgs
          for i in [:args.size] do
            if i < finfo.paramInfo.size then
              let info := finfo.paramInfo[i]!
              if !explicitOnly || info.isExplicit then
                args ← args.modifyM i visit
            else
              args ← args.modifyM i visit
          if f.isConstOf ``Nat.succ && args.size == 1 && args[0]!.isRawNatLit then
            pure <| mkRawNatLit (args[0]!.rawNatLit?.get! + 1)
          else
            pure <| mkAppN f args
        -- `let`-bindings are normally substituted by WHNF, but they are left alone when `zeta` is off,
        -- so we must reduce their subterms here.
        | Expr.letE nm t v b nonDep => do
          let t' ← visit t
          -- Reduce body with the let-bound name in context to avoid name shadowing
          let v' ← withLocalDeclD nm t <| fun _ => visit v
          let nm ← bumpNameIfUsed nm
          -- TODO: we use an opaque `cdecl` since this case only runs when `zeta` is off anyway.
          -- Is this correct?
          let b' ← withLocalDeclD nm t' fun x => do
            let b' ← visit (b.instantiate1 x)
            pure <| b'.abstract #[x]
          let e' := Expr.letE nm t' v' b' nonDep
          pure e'
        | Expr.lam ..        => lambdaTelescope e fun xs b => do mkLambdaFVars xs (← visit b)
        | Expr.forallE ..    => forallTelescope e fun xs b => do mkForallFVars xs (← visit b)
        | Expr.proj n i s .. => pure <| mkProj n i (← visit s)
        -- TODO: this case is pretty awkward; what we really want is a positional mdata context, I think
        | Expr.mdata md (Expr.letE nm t v b nonDep) => do
          let t' ← visit t
          -- Reduce body with the let-bound name in context to avoid name shadowing
          let v' ← withLocalDeclD nm t <| fun _ => visit v
          let nm ← bumpNameIfUsed nm
          let b' ← withLocalDeclD nm t' fun x => do
            let b' ← visit (b.instantiate1 x)
            pure <| b'.abstract #[x]
          let e' := Expr.letE nm t' v' b' nonDep
          pure <| mkMData md e'
        | _                  => pure e
        return e'
  visit e |>.run

initialize
  registerTraceClass `Smt.reduce
  registerTraceClass `Smt.reduce.whnf
  registerTraceClass `Smt.reduce.whnfCore
  registerTraceClass `Smt.reduce.rec
  registerTraceClass `Smt.reduce.matcher
  registerTraceClass `Smt.reduce.smartUnfoldingReduce

end Smt

initialize Smt.whnfRef.set Smt.whnfImp
