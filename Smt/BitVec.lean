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

def mkZeroLit (w : Nat) : Term :=
  literalT <| String.pushn "#b" '0' w

@[smtTranslator] def replaceFun : Translator
  | app (const `BitVec.xor ..) .. => return symbolT "bvxor"
  | app (const `BitVec.shiftLeft ..) .. => return symbolT "bvshl"
  | app (const `BitVec.shiftRight ..) .. => return symbolT "bvlshr"
  | e@(app (const `BitVec.zero ..) w ..) => do
    let w ← Meta.whnf w
    let some w ← Meta.evalNat w |>.run
      | throwError "bitvector{indentD e}\nhas variable bitwidth"
    return mkZeroLit w
  -- | app (app (app (const `BitVec.lsb_get! ..) ..) t _) bit _ => do
  --   let bit ← Meta.whnf bit
  --   let some bit ← Meta.evalNat bit
  --     | throwError "found variable bit access {bit}"
  --   let bit := mkLit <| .natVal bit
  --   let extract := mkApp3 (mkConst `_) (mkConst `extract) bit bit
  --   let some t ← applyTranslators t | return none
  --   return (mkApp2 (mkConst "=") (mkApp extract t) (mkConst "#b0"))
  | _ => return none

end Smt.BitVec
