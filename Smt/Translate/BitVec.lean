/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Lean
import Qq
import Std

import Smt.Translate

namespace Smt.Translate.BitVec

open Lean Expr
open Qq
open Std
open Translator Term

def getWidth (e : Expr) : MetaM (Option Nat) := do
  let t : Q(Type) ← Meta.inferType e
  match t with
  | ~q(BitVec $w) => Meta.evalNat (← Meta.whnf w)
  | _             => return none

/-- Make a binary bitvector literal with value `n` and width `w`. -/
def mkLit (w : Nat) (n : Nat) : Term :=
  let bits := Nat.toDigits 2 n |>.take w
  literalT <| bits.foldl (init := "#b".pushn '0' (w - bits.length)) (·.push ·)

def reduceLit (n : Expr) (e : Expr) : TranslationM Nat := do
  let some n ← Meta.evalNat (← Meta.whnf n) |>.run
    | throwError "literal{indentD n}\nis not constant in{indentD e}"
  return n

def reduceWidth (w : Expr) (e : Expr) : TranslationM Nat := do
  let some w ← Meta.evalNat (← Meta.whnf w) |>.run
    | throwError "bitvector width{indentD w}\nis not constant in{indentD e}"
  return w

@[smt_translate] def translateType : Translator := fun (e : Q(Type)) => match e with
  | ~q(BitVec $w) => do
    let w ← Meta.whnf w
    let some w ← (Meta.evalNat w).run
      | throwError "bitvector type{indentD e}\nhas variable width"
    return mkApp2 (symbolT "_") (symbolT "BitVec") (literalT (toString w))
  | _             => return none

open BitVec in
@[smt_translate] def translateBitVec : Translator := fun e => do
  let some w ← getWidth e | return none
  let e : Q(BitVec $w) ← pure e
  match e with
  | ~q(@HShiftLeft.hShiftLeft (BitVec _) (BitVec _) _ _ $x $y)   =>
    return mkApp2 (symbolT "bvshl") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(@HShiftRight.hShiftRight (BitVec _) (BitVec _) _ _ $x $y) =>
    return mkApp2 (symbolT "bvlshr") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(@zeroExtend $v _ $x) =>
    let v ← reduceWidth v e
    return mkApp3 (symbolT "_") (symbolT "zero_extend") (literalT (toString (w - v))) (← applyTranslators! x)
  | ~q(@signExtend $v _ $x) =>
    let v ← reduceWidth v e
    return mkApp3 (symbolT "_") (symbolT "sign_extend") (literalT (toString (w - v))) (← applyTranslators! x)
  | ~q(BitVec.ofNat _ $n) => return mkLit w (← reduceLit n e)
  | ~q(OfNat.ofNat $n)    => return mkLit w (← reduceLit n e)
  | ~q(-$x)               => return appT (symbolT "bvneg") (← applyTranslators! x)
  | ~q(~~~$x)             => return appT (symbolT "bvnot") (← applyTranslators! x)
  | ~q($x + $y)           => return mkApp2 (symbolT "bvadd") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x - $y)           => return mkApp2 (symbolT "bvsub") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x * $y)           => return mkApp2 (symbolT "bvmul") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(smtUDiv $x $y)     => return mkApp2 (symbolT "bvudiv") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x % $y)           => return mkApp2 (symbolT "bvurem") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(smtSDiv $x $y)     => return mkApp2 (symbolT "bvsdiv") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(srem $x $y)        => return mkApp2 (symbolT "bvsrem") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(smod $x $y)        => return mkApp2 (symbolT "bvsmod") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x &&& $y)         => return mkApp2 (symbolT "bvand") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x ||| $y)         => return mkApp2 (symbolT "bvor") (← applyTranslators! x) (← applyTranslators! y)
  | ~q($x ^^^ $y)         => return mkApp2 (symbolT "bvxor") (← applyTranslators! x) (← applyTranslators! y)
  | _                     => return none

@[smt_translate] def translateProp : Translator := fun (e : Q(Prop)) => match e with
  | ~q(($x : BitVec _) < $y) => return mkApp2 (symbolT "bvult") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(($x : BitVec _) ≤ $y) => return mkApp2 (symbolT "bvule") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(($x : BitVec _) ≥ $y) => return mkApp2 (symbolT "bvuge") (← applyTranslators! x) (← applyTranslators! y)
  | ~q(($x : BitVec _) > $y) => return mkApp2 (symbolT "bvugt") (← applyTranslators! x) (← applyTranslators! y)
  | _                        => return none

@[smt_translate] def replaceFun : Translator
  | e@(app (const ``BitVec.zero _) w) => do
    let w ← reduceWidth w e
    if w == 0 then throwError "cannot emit bitvector literal{indentD e}\nof bitwidth 0"
    return mkLit w 0
  | e@(app (app (app (const ``BitVec.rotateLeft _) _) x) n) => do
    let n ← reduceLit n e
    return appT
      (mkApp2 (symbolT "_") (symbolT "rotate_left") (literalT (toString n)))
      (← applyTranslators! x)
  | e@(app (app (app (const ``BitVec.rotateRight _) _) x) n) => do
    let n ← reduceLit n e
    return appT
      (mkApp2 (symbolT "_") (symbolT "rotate_right") (literalT (toString n)))
      (← applyTranslators! x)
  | app (app (app (app (const ``HAppend.hAppend _) (app (const ``BitVec _) _)) _) _) _ => return symbolT "concat"
  | e@(app (app (app (const ``BitVec.extractLsb _) _) i) j) => do
    let i ← reduceLit i e
    let j ← reduceLit j e
    return mkApp3 (symbolT "_") (symbolT "extract") (literalT (toString i)) (literalT (toString j))
  | e@(app (app (const ``BitVec.replicate _) _) i) => do
    let i ← reduceLit i e
    return mkApp2 (symbolT "_") (symbolT "repeat") (literalT (toString i))
  | _ => return none

end Smt.Translate.BitVec
