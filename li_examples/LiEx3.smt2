;; Example 3 of Li, Passmore and Paulson, JAR 2019 (Univ_RCF_Example.thy, example_3).
;; The lemma states: there is a real x satisfying the formula below; this file
;; asserts the formula, whose satisfiability is the statement (no unsat proof).
;; Translated mechanically from the Isabelle source by scripts/gen_li_examples.py.
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun x () Real)
(assert (and
    (= (- (- (* x x x x x) x) 1) 0)
    (= (- (- (+ (+ (+ (+ (- (- (- (- (+ (* x x x x x x x x x x x x) (* (/ 425 23) (* x x x x x x x x x x x))) (* (/ 228 23) (* x x x x x x x x x x))) (* 2 (* x x x x x x x x))) (* (/ 896 23) (* x x x x x x x))) (* (/ 394 23) (* x x x x x x))) (* (/ 456 23) (* x x x x x))) (* x x x x)) (* (/ 471 23) (* x x x))) (* (/ 645 23) (* x x))) (* (/ 31 23) x)) (/ 228 23)) 0)
    (>= (- (+ (* x x x) (* 22 (* x x))) 31) 0)
    (> (+ (- (- (* x x x x x x x x x x x x x x x x x x x x x x) (* (/ 234 567) (* x x x x x x x x x x x x x x x x x x x x))) (* 419 (* x x x x x x x x x x))) 1948) 0)))
(check-sat)
(exit)
