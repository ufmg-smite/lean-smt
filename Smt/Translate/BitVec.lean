/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Lean
import Std

import Smt.Translate.Translator

namespace Smt.Translate.BitVec

open Lean Expr
open Std
open Translator Term

@[smtTranslator] def replaceType : Translator
  | e@(app (const ``BitVec _) n) => do
    let n ← Meta.whnf n
    let some n ← Meta.evalNat n |>.run
      | throwError "bitvector type{indentD e}\nhas variable width"
    return mkApp2 (symbolT "_") (symbolT "BitVec") (literalT (toString n))
  | _ => return none

/-- Make a binary bitvector literal with value `n` and width `w`. -/
def mkLit (w : Nat) (n : Nat) : Term :=
  let bits := Nat.toDigits 2 n |>.take w
  literalT <| bits.foldl (init := "#b".pushn '0' (w - bits.length)) (·.push ·)

@[smtTranslator] def replaceEq : Translator
  -- TODO: we should really just support beq/bne across all types uniformly
  | app (app (const ``BEq.beq _) (app (const ``BitVec _) _)) _ => return symbolT "="
  | app (app (app (app (const ``bne _) (app (const ``BitVec _) _)) _) e) e' =>
    return appT (symbolT "not") (mkApp2 (symbolT "=") (← applyTranslators! e) (← applyTranslators! e'))
  | _ => return none

@[smtTranslator] def replaceFun : Translator
  | e@(app (const ``BitVec.zero _) w) => do
    let w ← reduceWidth w e
    if w == 0 then throwError "cannot emit bitvector literal{indentD e}\nof bitwidth 0"
    return mkLit w 0
  | e@(app (app (const ``BitVec.ofNat _) w) n) => do
    let w ← reduceWidth w e
    let n ← reduceLit n e
    if w == 0 then throwError "cannot emit bitvector literal{indentD e}\nof bitwidth 0"
    return mkLit w n
  | app (const ``BitVec.add _) _            => return symbolT "bvadd"
  | app (const ``BitVec.sub _) _            => return symbolT "bvsub"
  | app (const ``BitVec.mul _) _            => return symbolT "bvmul"
  | app (const ``BitVec.umod _) _           => return symbolT "bvurem"
  | app (const ``BitVec.udiv _) _           => return symbolT "bvudiv"
  | app (const ``BitVec.ult _) _            => return symbolT "bvult"
  | app (const ``BitVec.ule _) _            => return symbolT "bvule"
  | app (const ``BitVec.not _) _            => return symbolT "bvnot"
  | app (const ``BitVec.and _) _            => return symbolT "bvand"
  | app (const ``BitVec.or _) _             => return symbolT "bvor"
  | app (const ``BitVec.xor _) _            => return symbolT "bvxor"
  | e@(app (app (app (const ``BitVec.shiftLeft _) w) x) n) => do
    let w ← reduceWidth w e
    let n ← reduceLit n e
    if w == 0 then throwError "cannot emit bitvector literal{indentD e}\nof bitwidth 0"
    return mkApp2 (symbolT "bvshl") (← applyTranslators! x) (mkLit w n)
  | e@(app (app (app (const ``BitVec.ushiftRight _) w) x) n) => do
    let w ← reduceWidth w e
    let n ← reduceLit n e
    if w == 0 then throwError "cannot emit bitvector literal{indentD e}\nof bitwidth 0"
    return mkApp2 (symbolT "bvlshr") (← applyTranslators! x) (mkLit w n)
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
  | app (app (const ``BitVec.append _) _) _ => return symbolT "concat"
  | e@(app (app (app (const ``BitVec.extractLsb _) _) i) j) => do
    let i ← reduceLit i e
    let j ← reduceLit j e
    return mkApp3 (symbolT "_") (symbolT "extract") (literalT (toString i)) (literalT (toString j))
  | e@(app (app (const ``BitVec.replicate _) _) i) => do
    let i ← reduceLit i e
    return mkApp2 (symbolT "_") (symbolT "repeat") (literalT (toString i))
  | e@(app (app (const ``BitVec.zeroExtend _) _) i) => do
    let i ← reduceLit i e
    return mkApp2 (symbolT "_") (symbolT "zero_extend") (literalT (toString i))
  | e@(app (app (const ``BitVec.signExtend _) _) i) => do
    let i ← reduceLit i e
    return mkApp2 (symbolT "_") (symbolT "sign_extend") (literalT (toString i))
  | _ => return none
where
  reduceWidth (w : Expr) (e : Expr) : TranslationM Nat := do
    let some w ← Meta.evalNat (← Meta.whnf w) |>.run
      | throwError "bitvector width{indentD w}\nis not constant in{indentD e}"
    return w
  reduceLit (n : Expr) (e : Expr) : TranslationM Nat := do
    let some n ← Meta.evalNat (← Meta.whnf n) |>.run
      | throwError "literal{indentD n}\nis not constant in{indentD e}"
    return n

end Smt.Translate.BitVec
