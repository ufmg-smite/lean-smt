;; Example 2 of Li, Passmore and Paulson, JAR 2019 (Univ_RCF_Example.thy, example_2).
;; The lemma states: for all real x, the formula below holds; this file asserts
;; its negation, which is unsat.
;; Translated mechanically from the Isabelle source by scripts/gen_li_examples.py.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-fun x () Real)
(assert (not (or
    (not (and
    (> (* (* (- x 2) (- x 2)) (+ (- x) 4)) 0)
    (>= (* (* x x) (* (- x 3) (- x 3))) 0)
    (>= (- x 1) 0)
    (> (+ (- (* (- x 3) (- x 3))) 1) 0)))
    (>= (* (* (- (- x (/ 11 12))) (- (- x (/ 11 12))) (- (- x (/ 11 12)))) (* (- x (/ 41 10)) (- x (/ 41 10)) (- x (/ 41 10)))) 0))))
(check-sat)
(exit)
