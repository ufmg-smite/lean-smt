import Smt
import Smt.Real

/-!
Example 4 of Li, Passmore and Paulson, "Deciding univariate polynomial problems using untrusted
certificates in Isabelle/HOL" (JAR 2019), translated mechanically from `example_4` in
`Univ_RCF_Example.thy` (Isabelle `univ_rcf` development, Wenda Li) by
`scripts/gen_li_examples.py`. Timing recorded in the Isabelle file: univ_rcf 1.6s; univ_rcf_cert 0.1.
Powers are written as products: the `smt` tactic currently fails on `x ^ n` over `Real`.
-/

set_option maxHeartbeats 4000000 in
lemma li_example_4 (x : Real) :
    (x > 0 ∨
      (((-((61 * x) / 9)) + ((5 * (x * x)) / 9)) + ((20 * (x * x * x)) / 9)) > (-4) ∨
      1 ≤ x ∨
      x ≤ 0 ∨
      ((-((19 * x) / 9)) + ((10 * (x * x)) / 9)) ≤ (-1) ∨
      (((-((13 * x) / 9)) + ((31 * (x * x)) / 45)) + ((x * x * x) / 18)) ≤ (-(7 / 10)) ∨
      (((-((61 * x) / 9)) + ((5 * (x * x)) / 9)) + ((20 * (x * x * x)) / 9)) ≤ (-4)) := by
  smt

#print axioms li_example_4
