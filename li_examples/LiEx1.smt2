;; Example 1 of Li, Passmore and Paulson, JAR 2019 (Univ_RCF_Example.thy, example_1).
;; The lemma states: for all real x, the formula below holds; this file asserts
;; its negation, which is unsat.
;; Translated mechanically from the Isabelle source by scripts/gen_li_examples.py.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-fun x () Real)
(assert (not (or
    (not (and
    (>= x (- 9))
    (< x 10)
    (> (* x x x x) 0)))
    (> (* x x x x x x x x x x x x) 0))))
(check-sat)
(exit)
