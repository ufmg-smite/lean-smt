;; Example 4 of Li, Passmore and Paulson, JAR 2019 (Univ_RCF_Example.thy, example_4).
;; The lemma states: for all real x, the formula below holds; this file asserts
;; its negation, which is unsat.
;; Translated mechanically from the Isabelle source by scripts/gen_li_examples.py.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-fun x () Real)
(assert (not (or
    (> x 0)
    (> (+ (+ (- (/ (* 61 x) 9)) (/ (* 5 (* x x)) 9)) (/ (* 20 (* x x x)) 9)) (- 4))
    (<= 1 x)
    (<= x 0)
    (<= (+ (- (/ (* 19 x) 9)) (/ (* 10 (* x x)) 9)) (- 1))
    (<= (+ (+ (- (/ (* 13 x) 9)) (/ (* 31 (* x x)) 45)) (/ (* x x x) 18)) (- (/ 7 10)))
    (<= (+ (+ (- (/ (* 61 x) 9)) (/ (* 5 (* x x)) 9)) (/ (* 20 (* x x x)) 9)) (- 4)))))
(check-sat)
(exit)
