import Lean.Elab.Command
import Lean.Elab.Eval

import Smt.Data.BitVec
import Smt.Tactic.WHNFSmt

open Lean Elab Meta Term Command

unsafe def evalConfigUnsafe (s : Syntax) : TermElabM Smt.Config := do
  Term.evalTerm Smt.Config (mkConst ``Smt.Config) s

@[implementedBy evalConfigUnsafe]
opaque evalConfig (s : Syntax) : TermElabM Smt.Config

private def elabReduceCmd
    (f : Expr → Smt.ReductionM Expr) (cfg? : Syntax) (check? : Option Syntax) (t : TSyntax `term)
    : CommandElabM Unit :=
  liftTermElabM none do
    let cfg : Smt.Config ←
      if cfg?.getNumArgs > 0 then evalConfig cfg?[1]
      else pure {}
    let e ← Term.elabTerm t none
    let e' ← f e |>.run cfg
    logInfo m!"{e}\n==>\n{e'}"
    if check?.isSome then
      if ← isDefEq e e' then
        logInfo "defeq ✔️"
      else
        logError "defeq ❌"

elab "#reduceTranslucent" cfg?:optional("(config := " term ")") check?:optional("checking") t:term : command =>
  elabReduceCmd Smt.reduce cfg? check? t

/-- Note that the evaluation order is different, so this is not really Lean-WHNF anymore. -/
elab "#whnfTranslucent" cfg?:optional("(config := " term ")") check?:optional("checking") t:term : command => do
  elabReduceCmd Smt.whnf cfg? check? t

/-- Simulates a locally opaque definition. -/
opaque stuck : Nat → Nat → Nat

/-! Motivating issue: inlining let-bindings during reduction can cause exponential growth,
in particular in the presence of loops. -/

def exponentialLoop (k : Nat) : Nat := Id.run do
  let mut m := 0
  for _ in List.range k do
    m := stuck m m
  return m

/- exponentialLoop 2
==>
stuck (stuck 0 0) (stuck 0 0) -/

/- exponentialLoop 3
==>
stuck (stuck (stuck 0 0) (stuck 0 0)) (stuck (stuck 0 0) (stuck 0 0)) -/
#reduceTranslucent exponentialLoop 3

/-! With zeta-reduction globally off, we can avoid this issue.
Examples from fiat-crypto paper. -/

def num := List Nat

def add : num → num → num
  | a :: as, b :: bs =>
    let x := stuck a b
    x :: add as bs
  | as, [] => as
  | [], bs => bs

/- add [1, 2, 3] [4, 5, 6]
==>
let x := stuck 1 4;
x ::
  let x := stuck 2 5;
  x ::
    let x := stuck 3 6;
    [x] -/
#reduceTranslucent (config := {zeta := false}) add [1, 2, 3] [4, 5, 6]

def addCps : num → num → (num → α) → α
  | a::as, b::bs, k =>
    let n := stuck a b
    addCps as bs (λ l => k (n :: l))
  | as, [], k => k as
  | [], bs, k => k bs

/- addCps [1, 2, 3] [4, 5, 6] fun l => l
==>
let n := stuck 1 4;
let n_1 := stuck 2 5;
let n_2 := stuck 3 6;
[n, n_1, n_2] -/
#reduceTranslucent (config := {zeta := false}) addCps [1, 2, 3] [4, 5, 6] (fun l => l)

/-! However this interacts poorly with macros by keeping around all their auxiliary structure. -/

/- exponentialLoop 3
==>
let m := 0;
let m :=
  let col := [0, 1, 2];
  List.forIn.loop
    (fun x r =>
      let m := r;
      let m := stuck m m;
      ForInStep.yield m)
    col m;
m -/
#reduceTranslucent (config := {zeta := false}) exponentialLoop 3

/-! Instead, we can introduce a locally opaque let binding and only disable zeta on these.
Fiat-crypto examples with locally opaque let. -/

def addOpaque : num → num → num
  | a :: as, b :: bs =>
    let_opaque x := stuck a b
    x :: addOpaque as bs
  | as, [] => as
  | [], bs => bs

/- addOpaque [1, 2, 3] [4, 5, 6]
==>
let x := stuck 1 4;
x ::
  let x := stuck 2 5;
  x ::
    let x := stuck 3 6;
    [x] -/
#reduceTranslucent addOpaque [1,2,3] [4,5,6]

def addOpaqueCps : num → num → (num → α) → α
  | a::as, b::bs, k =>
    let_opaque n := stuck a b
    addOpaqueCps as bs (λ l => k (n :: l))
  | as, [], k => k as
  | [], bs, k => k bs

/- addOpaqueCps [1, 2, 3] [4, 5, 6] fun l => l
==>
let n := stuck 1 4;
let n_1 := stuck 2 5;
let n_2 := stuck 3 6;
[n, n_1, n_2] -/
#reduceTranslucent addOpaqueCps [1, 2, 3] [4, 5, 6] (fun l => l)

/-! With locally opaque let and the right `ForIn` instance, we get CPS for free.
Note the linear growth of the term and lack of auxiliary macro fluff. -/

section

@[inline] protected def List.forInOpaque
    {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (as : List α) (init : β) (f : α → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop
    | [], b    => pure b
    | a::as, b => do
      match (← f a b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b =>
        let_opaque arg := b;
        loop as arg
  loop as init

local instance (priority := default) : ForIn m (List α) α where
  forIn := List.forInOpaque

def loopCustomForIn (k : Nat) : Nat := Id.run do
  let mut m := 0
  for _ in List.range k do
    m := stuck m m
  return m

/- loopCustomForIn 3
==>
let arg := stuck 0 0;
let arg := stuck arg arg;
let arg := stuck arg arg;
arg -/
#reduceTranslucent loopCustomForIn 3

def loopManyCustomForIn (k : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 0
  for _ in List.range k do
    a := stuck a a
    b := stuck b b
  return a

/-! Unfortunately this still breaks in the presence of many-variable state
which gets compiled to a product type. -/

/- loopManyCustomForIn 3
==>
(let arg := { fst := 0, snd := 0 };
  let arg := { fst := Nat.add arg.1 arg.1, snd := Nat.add arg.2 arg.2 };
  let arg := { fst := Nat.add arg.1 arg.1, snd := Nat.add arg.2 arg.2 };
  arg).1 -/
#reduceTranslucent loopManyCustomForIn 3

end -- disable custom ForIn instance

/-! We can try hand-compiling the copied definition by introducing `let_opaque` in the right places. -/

def loopManyManual (k : Nat) : Nat := Id.run 
  (let a := 0;
  let b := 0;
  do
  let r ←
    (let col := List.range k;
      forIn col { fst := a, snd := b : Nat × Nat } fun _ r =>
        let a := r.fst;
        let b := r.snd;
        let_opaque a := stuck a a;
        let_opaque b := stuck b b;
        do
        pure PUnit.unit
        pure (ForInStep.yield { fst := a, snd := b }))
  match r with
    | { fst := a, snd := _ } => pure a)

/-! But the reduction is a mess. -/

/- loopManyManual 1
==>
((fun {β} motive a h_1 h_2 => ForInStep.rec (fun a => h_1 a) (fun a => h_2 a) a) (fun a => Id (Nat × Nat))
    (let a := 0;
    let b := 0;
    ForInStep.yield (a, b))
    (fun b => b) fun b =>
    let arg := b;
    arg).1 -/
#reduceTranslucent loopManyManual 1

/-! The issue is that we do not have let-lifting. By enabling it, we get a linear expression
without auxiliary lets. -/

/-
loopManyManual 2
==>
let a := stuck 0 0;
let b := stuck 0 0;
let a := stuck a a;
let b := stuck b b;
a
-/
#reduceTranslucent (config := {letPushElim := true}) loopManyManual 2

/-! Let-lifting is not a single rule but rather a whole bunch of them.

```lean
f ⤳ (let_opaque x := v; f')
-------------------------------
f e ⤳ let_opaque x := v; f' e  
```

```lean
e ⤳ (let_opaque x := v; e')
------------------------------
f e ⤳ let_opaque x := v; f e'
```

```lean
c ⤳ (let_opaque x := v; c')
----------------------------------------
c.proj i ⤳ let_opaque x := v; c'.proj i
```

And more for reducing recursor applications as well as smart-unfolding of matchers.
-/

-- TODO: atomic test cases
