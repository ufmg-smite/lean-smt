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
  | e@(app (const `BitVec ..) n ..) => do
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
  | app (app (const `BEq.beq ..) (app (const `BitVec ..) ..) ..) .. => return symbolT "="
  | app (app (app (app (const `bne ..) (app (const `BitVec ..) ..) ..) ..) e ..) e' .. =>
    return appT (symbolT "not") (mkApp2 (symbolT "=") (← applyTranslators! e) (← applyTranslators! e'))
  | _ => return none

@[smtTranslator] def replaceFun : Translator
  | app (const `BitVec.xor ..) ..             => return symbolT "bvxor"
  | app (const `BitVec.shiftLeft ..) ..       => return symbolT "bvshl"
  | app (const `BitVec.shiftRight ..) ..      => return symbolT "bvlshr"
  | app (app (const `BitVec.append ..) ..) .. => return symbolT "concat"
  | app (app (app (const `BitVec.extract ..) ..) i ..) j .. => do
    let some i ← Meta.evalNat (← Meta.whnf i) |>.run
      | throwError "index literal{indentD i}\nis not constant"
    let some j ← Meta.evalNat (← Meta.whnf j) |>.run
      | throwError "index literal{indentD j}\nis not constant"
    return mkApp3 (symbolT "_") (symbolT "extract") (literalT (toString i)) (literalT (toString j))
  | e@(app (const `BitVec.zero ..) w ..) => do
    let some w ← Meta.evalNat (← Meta.whnf w) |>.run
      | throwError "bitvector{indentD e}\nhas variable bitwidth"
    if w == 0 then throwError "cannot emit bitvector literal{indentD e}\nof bitwidth 0"
    return mkLit w 0
  | e@(app (app (const `BitVec.ofNat ..) w ..) n ..) => do
    let some w ← Meta.evalNat (← Meta.whnf w) |>.run
      | throwError "bitvector{indentD e}\nhas variable bitwidth"
    let some n ← Meta.evalNat (← Meta.whnf n) |>.run
      | throwError "nat literal{indentD n}\nis not constant"
    if w == 0 then throwError "cannot emit bitvector literal{indentD e}\nof bitwidth 0"
    return mkLit w n
  | _ => return none

end Smt.BitVec
