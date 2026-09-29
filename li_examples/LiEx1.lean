import Smt
import Smt.Real

/-!
Example 1 of Li, Passmore and Paulson, "Deciding univariate polynomial problems using untrusted
certificates in Isabelle/HOL" (JAR 2019), translated mechanically from `example_1` in
`Univ_RCF_Example.thy` (Isabelle `univ_rcf` development, Wenda Li) by
`scripts/gen_li_examples.py`. Timing recorded in the Isabelle file: univ_rcf 1.5s; univ_rcf_cert 0.0s.
Powers are written as products: the `smt` tactic currently fails on `x ^ n` over `Real`.
-/

set_option maxHeartbeats 4000000 in
lemma li_example_1 (x : Real) :
    (¬((x ≥ (-9) ∧
      x < 10 ∧
      (x * x * x * x) > 0)) ∨
      (x * x * x * x * x * x * x * x * x * x * x * x) > 0) := by
  smt

#print axioms li_example_1
