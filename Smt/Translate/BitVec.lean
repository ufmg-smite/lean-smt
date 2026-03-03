/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Smt.Recognizers
import Smt.Translate

namespace Smt.Translate.BitVec

open Lean Expr
open Translator

/-- Make a binary bitvector literal with value `n` and width `w`. -/
private def mkLit (w : Nat) (n : Nat) : Term :=
  let bits := Nat.toDigits 2 n |>.take w
  .literalT <| bits.foldl (init := "#b".pushn '0' (w - bits.length)) (·.push ·)

private def reduceLit (n : Expr) (e : Expr) : TranslationM Nat := do
  let some n ← (Meta.evalNat (← Meta.whnf n)).run | throwError "literal{indentD n}\nis not constant in{indentD e}"
  return n

private def reduceWidth (w : Expr) (e : Expr) : TranslationM Nat := do
  let some w' ← (Meta.evalNat w).run | throwError "bitvector width{indentD w}\nis not constant in{indentD e}"
  if w' == 0 then
    throwError "bitvector width{indentD w}\nis 0 in{indentD e}"
  return w'

private def reduceBitVecWidth? (e : Expr) : MetaM (Option Nat) := do
  let some w := e.app1? ``BitVec | return none
  let some w' ← (Meta.evalNat w).run | throwError "bitvector type{indentD e}\nhas variable width"
  if w' == 0 then
    throwError "bitvector width{indentD w}\nis 0 in{indentD e}"
  return w'

@[smt_translate] def translateType : Translator := fun e => do
  if let some w ← reduceBitVecWidth? e then
    return some (.mkApp2 (.symbolT "_") (.symbolT "BitVec") (.literalT (toString w)))
  else
    return none

@[smt_translate] def translateBitVec : Translator := fun e => do match e with
  | mkApp6 (.const ``HShiftLeft.hShiftLeft [0, 0, 0]) α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (.mkApp2 (.symbolT "bvshl") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp6 (.const ``HShiftRight.hShiftRight [0, 0, 0]) α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (.mkApp2 (.symbolT "bvlshr") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp3 (.const ``BitVec.zeroExtend []) w v x =>
    let w ← reduceWidth w x
    let v ← reduceWidth v e
    return some (.mkApp3 (.symbolT "_") (.symbolT "zero_extend") (.literalT (toString (v - w))) (← applyTranslators! x))
  | mkApp3 (.const ``BitVec.signExtend []) w v x =>
    let w ← reduceWidth w x
    let v ← reduceWidth v e
    return some (.mkApp3 (.symbolT "_") (.symbolT "sign_extend") (.literalT (toString (v - w))) (← applyTranslators! x))
  | mkApp2 (.const ``BitVec.ofNat []) w n =>
    let w ← reduceWidth w e
    let n ← reduceLit n e
    return some (mkLit w n)
  | mkApp3 (.const ``OfNat.ofNat [0]) α n _ =>
    let some w ← reduceBitVecWidth? α | return none
    let n ← reduceLit n e
    return some (mkLit w n)
  | mkApp3 (.const ``Neg.neg [0]) α _ x =>
    let some _ ← reduceBitVecWidth? α | return none
    return some (.appT (.symbolT "bvneg") (← applyTranslators! x))
  | mkApp3 (.const ``Complement.complement [0]) α _ x =>
    let some _ ← reduceBitVecWidth? α | return none
    return some (.appT (.symbolT "bvnot") (← applyTranslators! x))
  | mkApp6 (.const ``HAdd.hAdd [0, 0, 0]) α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (.mkApp2 (.symbolT "bvadd") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp6 (.const ``HSub.hSub [0, 0, 0]) α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (.mkApp2 (.symbolT "bvsub") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp6 (.const ``HMul.hMul [0, 0, 0]) α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (.mkApp2 (.symbolT "bvmul") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp3 (.const ``BitVec.smtUDiv []) _ x y =>
    return some (.mkApp2 (.symbolT "bvudiv") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp6 (.const ``HMod.hMod []) α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (.mkApp2 (.symbolT "bvurem") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp3 (.const ``BitVec.smtSDiv []) w x y =>
    _ ← reduceWidth w e
    return some (.mkApp2 (.symbolT "bvsdiv") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp3 (.const ``BitVec.srem []) w x y =>
    _ ← reduceWidth w e
    return some (.mkApp2 (.symbolT "bvsrem") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp3 (.const ``BitVec.smod []) w x y =>
    _ ← reduceWidth w e
    return some (.mkApp2 (.symbolT "bvsmod") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp6 (.const ``HAnd.hAnd [0, 0, 0]) α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (.mkApp2 (.symbolT "bvand") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp6 (.const ``HOr.hOr [0, 0, 0]) α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (.mkApp2 (.symbolT "bvor") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp6 (.const ``HXor.hXor [0, 0, 0]) α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (.mkApp2 (.symbolT "bvxor") (← applyTranslators! x) (← applyTranslators! y))
  | .app (.const ``BitVec.zero []) w => do
    let w ← reduceWidth w e
    return mkLit w 0
  | mkApp3 (.const ``BitVec.rotateLeft []) w x n =>
    _ ← reduceWidth w e
    return some (.appT (.mkApp2 (.symbolT "_") (.symbolT "rotate_left") (.literalT (toString n)))
                       (← applyTranslators! x))
  | mkApp3 (.const ``BitVec.rotateRight []) w x n =>
    _ ← reduceWidth w e
    return some (.appT (.mkApp2 (.symbolT "_") (.symbolT "rotate_right") (.literalT (toString n)))
                       (← applyTranslators! x))
  | mkApp6 (.const ``HAppend.hAppend [0, 0, 0]) α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (.mkApp2 (.symbolT "concat") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp3 (.const ``BitVec.replicate []) w i x =>
    _ ← reduceWidth w e
    let i ← reduceLit i e
    return some (.appT (.mkApp2 (.symbolT "_") (.symbolT "repeat") (.literalT (toString i)))
                       (← applyTranslators! x))
  | _                  => return none

@[smt_translate] def translateProp : Translator := fun e => do match e with
  | mkApp4 (.const ``LT.lt [0]) α _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    return some (.mkApp2 (.symbolT "bvult") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp4 (.const ``LE.le [0]) α _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    return some (.mkApp2 (.symbolT "bvule") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp4 (.const ``GE.ge [0]) α _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    return some (.mkApp2 (.symbolT "bvuge") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp4 (.const ``GT.gt [0]) α _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    return some (.mkApp2 (.symbolT "bvugt") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp3 (.const ``Eq [1]) _ (mkApp3 (.const ``BitVec.slt []) w x y) (.const ``true []) =>
    _ ← reduceWidth w e
    return some (.mkApp2 (.symbolT "bvslt") (← applyTranslators! x) (← applyTranslators! y))
  | mkApp3 (.const ``Eq [1]) _ (mkApp3 (.const ``BitVec.sle []) w x y) (.const ``true []) =>
    _ ← reduceWidth w e
    return some (.mkApp2 (.symbolT "bvsle") (← applyTranslators! x) (← applyTranslators! y))
  | _                        => return none

end Smt.Translate.BitVec
