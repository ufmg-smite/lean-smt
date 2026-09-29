;; Example 7 of Li, Passmore and Paulson, JAR 2019 (Univ_RCF_Example.thy, example_7).
;; The lemma states: for all real x, the disjunction below holds; this file asserts its
;; negation, which is unsat. Translated mechanically from the Isabelle source.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-fun x () Real)
(assert (not (or
  (< x (- 1))
  (> 0 x)
  (> (+ (/ (* 41613 x) 2) (* 26169 (* x x)) (/ (* 64405 (* x x x)) 4) (* 4983 (* x x x x)) (/ (* 7083 (* x x x x x)) 10) (/ (* 1207 (* x x x x x x)) 35) (/ (* x x x x x x x) 8)) (- 6435))
  (<= (+ (* 11821609800 x) (* 22461058620 (* x x)) (* 35 (* x x x x x x x x x x x x))) (+ (* 4171407240 (* x x x)) (* 45938678170 (* x x x x)) (* 54212099480 (* x x x x x)) (* 31842714428 (* x x x x x x)) (* 10317027768 (* x x x x x x x)) (* 1758662439 (* x x x x x x x x)) (* 144537452 (* x x x x x x x x x)) (* 5263834 (* x x x x x x x x x x)) (* 46204 (* x x x x x x x x x x x))))
  (<= x 0)
  (<= (+ (* 9609600 x) (* 45805760 (* x x)) (* 92372280 (* x x x)) (* 102560612 (* x x x x)) (* 68338600 (* x x x x x)) (* 27930066 (* x x x x x x)) (* 6857016 (* x x x x x x x)) (* 938908 (* x x x x x x x x)) (* 58568 (* x x x x x x x x x)) (* 753 (* x x x x x x x x x x))) 0)
  (<= (+ (* 788107320 x) (* 1101329460 (* x x)) (* 10 (* x x x x x x x x x x x))) (+ (* 782617220 (* x x x)) (* 2625491260 (* x x x x)) (* 2362290448 (* x x x x x)) (* 1063536663 (* x x x x x x)) (* 240283734 (* x x x x x x x)) (* 24397102 (* x x x x x x x x)) (* 1061504 (* x x x x x x x x x)) (* 9179 (* x x x x x x x x x x))))
  (<= (+ (* 90935460 x) (* 81290790 (* x x)) (* 5 (* x x x x x x x x x x))) (+ (* 125595120 (* x x x)) (* 237512625 (* x x x x)) (* 161529144 (* x x x x x)) (* 51834563 (* x x x x x x)) (* 6846880 (* x x x x x x x)) (* 356071 (* x x x x x x x x)) (* 2828 (* x x x x x x x x x))))
  (<= (+ (* 640640 x) (* 2735040 (* x x)) (* 4837448 (* x x x)) (* 4581220 (* x x x x)) (* 2505504 (* x x x x x)) (* 794964 (* x x x x x x)) (* 138652 (* x x x x x x x)) (* 11237 (* x x x x x x x x)) (* 207 (* x x x x x x x x x))) 0)
  (<= (* 5 (* x x x x x x x x)) (+ (* 73920 x) (* 238560 (* x x)) (* 303324 (* x x x)) (* 192458 (* x x x x)) (* 63520 (* x x x x x)) (* 10261 (* x x x x x x)) (* 608 (* x x x x x x x))))
  (<= (+ (* 73920 x) (* 278880 (* x x)) (* 424284 (* x x x)) (* 332962 (* x x x x)) (* 142928 (* x x x x x)) (* 32711 (* x x x x x x)) (* 3514 (* x x x x x x x)) (* 98 (* x x x x x x x x))) 0)
  (<= x (- 1))
)))
(check-sat)
(exit)
