/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Lean
import Smt.Translator
import Smt.Data.BitVec

namespace Smt.BitVec

open Lean Expr
open Translator Term

@[smtTranslator] def replaceType : Translator
  | e@(app (const ``BitVec _) n) => do
    let n ← Meta.whnf n
    let some n ← Meta.evalNat n |>.run
      | throwError "bitvector type{indentD e}\nhas variable width"
    return mkApp2 (symbolT "_") (symbolT "BitVec") (literalT (toString n))
  | _ => return none

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
  | app (app (const ``BitVec.append _) _) _ => return symbolT "concat"
  | app (const ``BitVec.and _) _            => return symbolT "bvand"
  | app (const ``BitVec.or _) _             => return symbolT "bvor"
  | app (const ``BitVec.xor _) _            => return symbolT "bvxor"
  | e@(app (app (app (const ``BitVec.shiftLeft _) w) x) n) => do
    let w ← reduceWidth w e
    let n ← reduceLit n e
    if w == 0 then throwError "cannot emit bitvector literal{indentD e}\nof bitwidth 0"
    return mkApp2 (symbolT "bvshl") (← applyTranslators! x) (mkLit w n)
  | e@(app (app (app (const ``BitVec.shiftRight _) w) x) n) => do
    let w ← reduceWidth w e
    let n ← reduceLit n e
    if w == 0 then throwError "cannot emit bitvector literal{indentD e}\nof bitwidth 0"
    return mkApp2 (symbolT "bvlshr") (← applyTranslators! x) (mkLit w n)
  | e@(app (app (app (const ``BitVec.extract _) _) i) j) => do
    let i ← reduceLit i e
    let j ← reduceLit j e
    return mkApp3 (symbolT "_") (symbolT "extract") (literalT (toString i)) (literalT (toString j))
  | e@(app (const ``BitVec.zero _) w) => do
    let w ← reduceWidth w e
    if w == 0 then throwError "cannot emit bitvector literal{indentD e}\nof bitwidth 0"
    return mkLit w 0
  | e@(app (app (const ``BitVec.ofNat _) w) n) => do
    let w ← reduceWidth w e
    let n ← reduceLit n e
    if w == 0 then throwError "cannot emit bitvector literal{indentD e}\nof bitwidth 0"
    return mkLit w n
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

end Smt.BitVec
