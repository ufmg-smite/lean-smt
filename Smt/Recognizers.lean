/-
Copyright (c) 2021-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean.Meta.Basic
import Lean.Util.Recognizers

namespace Lean.Expr

def app5? (e : Expr) (fName : Name) : Option (Expr × Expr × Expr × Expr × Expr) :=
  if e.isAppOfArity fName 5 then
    some (e.appFn!.appFn!.appFn!.appFn!.appArg!, e.appFn!.appFn!.appFn!.appArg!, e.appFn!.appFn!.appArg!, e.appFn!.appArg!, e.appArg!)
  else
    none

def or? (p : Expr) : Option (Expr × Expr) :=
  p.app2? ``Or

def imp? (p : Expr) : Lean.MetaM (Option (Expr × Expr)) := do
  let .forallE _ p q _ := p | return none
  if ← (isAProp p) <&&> (isAProp q) then
    return (p, q)
  else
    return none
where
  isAProp (e : Expr) : MetaM Bool := do
    return (← Meta.inferType e).isProp

def beq? (b : Expr) : Option (Expr × Expr × Expr) :=
  let_expr BEq.beq α _ a b := b | none
  return (α, a, b)

def bne? (b : Expr) : Option (Expr × Expr × Expr) :=
  let_expr bne α _ a b := b | none
  return (α, a, b)

def ltOf? (e : Expr) (α : Expr) : Option (Expr × Expr) :=
  let_expr LT.lt β _ x y := e | none
  if β == α then
    return (x, y)
  else
    none

def leOf? (e : Expr) (α : Expr) : Option (Expr × Expr) :=
  let_expr LE.le β _ x y := e | none
  if β == α then
    return (x, y)
  else
    none

def geOf? (e : Expr) (α : Expr) : Option (Expr × Expr) :=
  let_expr GE.ge β _ x y := e | none
  if β == α then
    return (x, y)
  else
    none

def gtOf? (e : Expr) (α : Expr) : Option (Expr × Expr) :=
  let_expr GT.gt β _ x y := e | none
  if β == α then
    return (x, y)
  else
    none

def natLitOf? (e : Expr) (α : Expr) : Option Nat :=
  let_expr OfNat.ofNat β n _ := e | none
  if β == α then
    n.rawNatLit?
  else
    none

def intCastOf? (e : Expr) (α : Expr) : Option Expr :=
  let_expr Int.cast β _ x := e | none
  if β == α then
    return x
  else
    none

def intFloorOf? (e : Expr) (α : Expr) : Option Expr := do
  let some (β, _, _, _, x) := e.app5? `Int.floor | none
  if β == α then
    return x
  else
    none

def negOf? (e : Expr) (α : Expr) : Option Expr :=
  let_expr Neg.neg β _ x := e | none
  if β == α then
    return x
  else
    none

def absOf? (e : Lean.Expr) (α : Expr) : Option Expr := do
  let some (β, _, _, x) := e.app4? `abs | none
  if β == α then
    return x
  else
    none

def hAddOf? (e : Expr) (α : Expr) (β : Expr) : Option (Expr × Expr) :=
  let_expr HAdd.hAdd γ δ _ _ x y := e | none
  if γ == α && δ == β then
    return (x, y)
  else
    none

def hSubOf? (e : Expr) (α : Expr) (β : Expr) : Option (Expr × Expr) :=
  let_expr HSub.hSub γ δ _ _ x y := e | none
  if γ == α && δ == β then
    return (x, y)
  else
    none

def hMulOf? (e : Expr) (α : Expr) (β : Expr) : Option (Expr × Expr) :=
  let_expr HMul.hMul γ δ _ _ x y := e | none
  if γ == α && δ == β then
    return (x, y)
  else
    none

def hDivOf? (e : Expr) (α : Expr) (β : Expr) : Option (Expr × Expr) :=
  let_expr HDiv.hDiv γ δ _ _ x y := e | none
  if γ == α && δ == β then
    return (x, y)
  else
    none

def hModOf? (e : Expr) (α : Expr) (β : Expr) : Option (Expr × Expr) :=
  let_expr HMod.hMod γ δ _ _ x y := e | none
  if γ == α && δ == β then
    return (x, y)
  else
    none

def hPowOf? (e : Expr) (α : Expr) (β : Expr) : Option (Expr × Expr) :=
  let_expr HPow.hPow γ δ _ _ x y := e | none
  if γ == α && δ == β then
    return (x, y)
  else
    none

def hAndOf? (e : Expr) (α : Expr) (β : Expr) : Option (Expr × Expr) :=
  let_expr HAnd.hAnd γ δ _ _ x y := e | none
  if γ == α && δ == β then
    return (x, y)
  else
    none

def hOrOf? (e : Expr) (α : Expr) (β : Expr) : Option (Expr × Expr) :=
  let_expr HOr.hOr γ δ _ _ x y := e | none
  if γ == α && δ == β then
    return (x, y)
  else
    none

def hXorOf? (e : Expr) (α : Expr) (β : Expr) : Option (Expr × Expr) :=
  let_expr HXor.hXor γ δ _ _ x y := e | none
  if γ == α && δ == β then
    return (x, y)
  else
    none

def hAppendOf? (e : Expr) (α : Expr) (β : Expr) : Option (Expr × Expr) :=
  let_expr HAppend.hAppend γ δ _ _ x y := e | none
  if γ == α && δ == β then
    return (x, y)
  else
    none

end Lean.Expr
