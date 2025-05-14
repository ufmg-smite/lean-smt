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
open Translator Term

/-- Make a binary bitvector literal with value `n` and width `w`. -/
private def mkLit (w : Nat) (n : Nat) : Term :=
  let bits := Nat.toDigits 2 n |>.take w
  literalT <| bits.foldl (init := "#b".pushn '0' (w - bits.length)) (·.push ·)

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
    return mkApp2 (symbolT "_") (symbolT "BitVec") (literalT (toString w))
  else
    return none

@[smt_translate] def translateBitVec : Translator := fun e => do match_expr e with
  | HShiftLeft.hShiftLeft α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (mkApp2 (symbolT "bvshl") (← applyTranslators! x) (← applyTranslators! y))
  | HShiftRight.hShiftRight α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (mkApp2 (symbolT "bvlshr") (← applyTranslators! x) (← applyTranslators! y))
  | BitVec.zeroExtend w v x =>
    let w ← reduceWidth w x
    let v ← reduceWidth v e
    return some (mkApp3 (symbolT "_") (symbolT "zero_extend") (literalT (toString (v - w))) (← applyTranslators! x))
  | BitVec.signExtend w v x =>
    let w ← reduceWidth w x
    let v ← reduceWidth v e
    return some (mkApp3 (symbolT "_") (symbolT "sign_extend") (literalT (toString (v - w))) (← applyTranslators! x))
  | BitVec.ofNat w n =>
    let w ← reduceWidth w e
    let n ← reduceLit n e
    return some (mkLit w n)
  | OfNat.ofNat α n _ =>
    let some w ← reduceBitVecWidth? α | return none
    let n ← reduceLit n e
    return some (mkLit w n)
  | Neg.neg α _ x =>
    let some _ ← reduceBitVecWidth? α | return none
    return some (appT (symbolT "bvneg") (← applyTranslators! x))
  | Complement.complement α _ x =>
    let some _ ← reduceBitVecWidth? α | return none
    return some (appT (symbolT "bvnot") (← applyTranslators! x))
  | HAdd.hAdd α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (mkApp2 (symbolT "bvadd") (← applyTranslators! x) (← applyTranslators! y))
  | HSub.hSub α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (mkApp2 (symbolT "bvsub") (← applyTranslators! x) (← applyTranslators! y))
  | HMul.hMul α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (mkApp2 (symbolT "bvmul") (← applyTranslators! x) (← applyTranslators! y))
  | BitVec.smtUDiv _ x y =>
    return some (mkApp2 (symbolT "bvudiv") (← applyTranslators! x) (← applyTranslators! y))
  | HMod.hMod α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (mkApp2 (symbolT "bvurem") (← applyTranslators! x) (← applyTranslators! y))
  | BitVec.smtSDiv w x y =>
    _ ← reduceWidth w e
    return some (mkApp2 (symbolT "bvsdiv") (← applyTranslators! x) (← applyTranslators! y))
  | BitVec.srem w x y =>
    _ ← reduceWidth w e
    return some (mkApp2 (symbolT "bvsrem") (← applyTranslators! x) (← applyTranslators! y))
  | BitVec.smod w x y =>
    _ ← reduceWidth w e
    return some (mkApp2 (symbolT "bvsmod") (← applyTranslators! x) (← applyTranslators! y))
  | HAnd.hAnd α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (mkApp2 (symbolT "bvand") (← applyTranslators! x) (← applyTranslators! y))
  | HOr.hOr α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (mkApp2 (symbolT "bvor") (← applyTranslators! x) (← applyTranslators! y))
  | HXor.hXor α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (mkApp2 (symbolT "bvxor") (← applyTranslators! x) (← applyTranslators! y))
  | BitVec.zero w => do
    let w ← reduceWidth w e
    return mkLit w 0
  | BitVec.rotateLeft w x n =>
    _ ← reduceWidth w e
    return appT (mkApp2 (symbolT "_") (symbolT "rotate_left") (literalT (toString n)))
                (← applyTranslators! x)
  | BitVec.rotateRight w x n =>
    _ ← reduceWidth w e
    return appT (mkApp2 (symbolT "_") (symbolT "rotate_right") (literalT (toString n)))
                (← applyTranslators! x)
  | HAppend.hAppend α β _ _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    let some _ ← reduceBitVecWidth? β | return none
    return some (mkApp2 (symbolT "concat") (← applyTranslators! x) (← applyTranslators! y))
  | BitVec.replicate w i x =>
    _ ← reduceWidth w e
    let i ← reduceLit i e
    return appT (mkApp2 (symbolT "_") (symbolT "repeat") (literalT (toString i)))
                (← applyTranslators! x)
  | _                  => return none

@[smt_translate] def translateProp : Translator := fun e => do match_expr e with
  | LT.lt α _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    return some (mkApp2 (symbolT "bvult") (← applyTranslators! x) (← applyTranslators! y))
  | LE.le α _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    return some (mkApp2 (symbolT "bvule") (← applyTranslators! x) (← applyTranslators! y))
  | GE.ge α _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    return some (mkApp2 (symbolT "bvuge") (← applyTranslators! x) (← applyTranslators! y))
  | GT.gt α _ x y =>
    let some _ ← reduceBitVecWidth? α | return none
    return some (mkApp2 (symbolT "bvugt") (← applyTranslators! x) (← applyTranslators! y))
  | _                        => return none

end Smt.Translate.BitVec
