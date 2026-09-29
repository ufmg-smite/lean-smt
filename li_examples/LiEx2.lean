import Smt
import Smt.Real

/-!
Example 2 of Li, Passmore and Paulson, "Deciding univariate polynomial problems using untrusted
certificates in Isabelle/HOL" (JAR 2019), translated mechanically from `example_2` in
`Univ_RCF_Example.thy` (Isabelle `univ_rcf` development, Wenda Li) by
`scripts/gen_li_examples.py`. Timing recorded in the Isabelle file: univ_rcf 1.5s; univ_rcf_cert 0.1s.
Powers are written as products: the `smt` tactic currently fails on `x ^ n` over `Real`.
-/

set_option maxHeartbeats 4000000 in
lemma li_example_2 (x : Real) :
    (¬(((((x - 2) * (x - 2)) * ((-x) + 4)) > 0 ∧
      ((x * x) * ((x - 3) * (x - 3))) ≥ 0 ∧
      (x - 1) ≥ 0 ∧
      ((-((x - 3) * (x - 3))) + 1) > 0)) ∨
      (((-(x - (11 / 12))) * (-(x - (11 / 12))) * (-(x - (11 / 12)))) * ((x - (41 / 10)) * (x - (41 / 10)) * (x - (41 / 10)))) ≥ 0) := by
  smt

#print axioms li_example_2
