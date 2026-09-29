import Smt
import Smt.Real

/-!
Example 3 of Li, Passmore and Paulson, "Deciding univariate polynomial problems using untrusted
certificates in Isabelle/HOL" (JAR 2019), translated mechanically from `example_3` in
`Univ_RCF_Example.thy` (Isabelle `univ_rcf` development, Wenda Li) by
`scripts/gen_li_examples.py`. Timing recorded in the Isabelle file: univ_rcf 1.5s; univ_rcf_cert 0.0s.
Powers are written as products: the `smt` tactic currently fails on `x ^ n` over `Real`.
-/

set_option maxHeartbeats 4000000 in
lemma li_example_3 :
    ∃ x : Real,
      ((((x * x * x * x * x) - x) - 1) = 0 ∧
      ((((((((((((x * x * x * x * x * x * x * x * x * x * x * x) + ((425 / 23) * (x * x * x * x * x * x * x * x * x * x * x))) - ((228 / 23) * (x * x * x * x * x * x * x * x * x * x))) - (2 * (x * x * x * x * x * x * x * x))) - ((896 / 23) * (x * x * x * x * x * x * x))) - ((394 / 23) * (x * x * x * x * x * x))) + ((456 / 23) * (x * x * x * x * x))) + (x * x * x * x)) + ((471 / 23) * (x * x * x))) + ((645 / 23) * (x * x))) - ((31 / 23) * x)) - (228 / 23)) = 0 ∧
      (((x * x * x) + (22 * (x * x))) - 31) ≥ 0 ∧
      ((((x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x) - ((234 / 567) * (x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x))) - (419 * (x * x * x * x * x * x * x * x * x * x))) + 1948) > 0) := by
  smt

#print axioms li_example_3
