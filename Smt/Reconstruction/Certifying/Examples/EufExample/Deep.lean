import Cdclt.Euf
import Cdclt.Array
import Cdclt.BV
import Cdclt.Quant
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

open proof
open proof.sort proof.term
open rules eufRules arrayRules bvRules quantRules

def U := atom 1000
def f := const 1000 (arrowN [U, U, U])
def p2 := const 1001 boolSort
def p3 := const 1002 boolSort
def p1 := const 1003 boolSort
def c := const 1004 U
def d := const 1005 U
def a := const 1006 U
def b := const 1007 U
def let1 := (eq a b)
def let2 := (eq c d)
def let3 := (term.and p1 top)
def let4 := (term.and p2 p3)
def let5 := (term.or (term.not p1) let4)
def let6 := (eq (appN f [a, c]) (appN f [b, d]))
def let7 := (term.not let6)
def let8 := (term.or (term.not p3) let7)
def let9 := (term.not let4)
def let10 := (term.not let2)
def let11 := (term.not let1)
def let12 := (term.and let1 let2)

theorem th0 : thHolds let1 -> thHolds let2 -> thHolds let3 -> thHolds let5 -> thHolds let8 -> holds [] :=
fun lean_a0 : thHolds let1 =>
fun lean_a1 : thHolds let2 =>
fun lean_a2 : thHolds let3 =>
fun lean_a3 : thHolds let5 =>
fun lean_a4 : thHolds let8 =>
have lean_s0 : holds ([let12, let11, let10]) := @cnfAndNeg ([let1, let2])
have lean_s1 : thHolds (orN [let11, let10, let6]) :=
  (scope (fun lean_a5 : thHolds let1 =>
    (scope (fun lean_a6 : thHolds let2 =>
      let lean_s1 := @refl f
      have lean_s2 : thHolds (eq b a) := symm lean_a5
      have lean_s3 : thHolds let1 := symm lean_s2
      let lean_s4 := cong lean_s1 lean_s3
      have lean_s5 : thHolds (eq d c) := symm lean_a6
      have lean_s6 : thHolds let2 := symm lean_s5
      have lean_s7 : thHolds let6 := cong lean_s4 lean_s6
      show thHolds let6 from lean_s7
  ))))
have lean_s2 : thHolds (implies let12 let6) := liftNOrToImp lean_s1 2 let6
have lean_s3 : thHolds (term.or (term.not let12) let6) := impliesElim lean_s2
let lean_s4 := clOr lean_s3
have lean_s5 : holds ([let11, let10, let6]) := R0 lean_s0 lean_s4 let12
have lean_s6 : holds ([let6, let11, let10]) := reorder lean_s5 ([2, 0, 1])
let lean_s7 := clOr lean_a4
have lean_s8 : holds ([let9, p3]) := @cnfAndPos ([p2, p3]) 1
have lean_s9 : holds ([p3, let9]) := reorder lean_s8 ([1, 0])
let lean_s10 := clOr lean_a3
have lean_s11 : thHolds (eq let3 p1) := thTrustValid
have lean_s12 : thHolds p1 := eqResolve lean_a2 lean_s11
let lean_s13 := clAssume lean_s12
have lean_s14 : holds ([let4]) := R1 lean_s10 lean_s13 p1
have lean_s15 : holds ([p3]) := R1 lean_s9 lean_s14 let4
have lean_s16 : holds ([let7]) := R1 lean_s7 lean_s15 p3
let lean_s17 := R0 lean_s6 lean_s16 let6
let lean_s18 := clAssume lean_a1
let lean_s19 := R1 lean_s17 lean_s18 let2
let lean_s20 := clAssume lean_a0
show holds [] from R1 lean_s19 lean_s20 let1


