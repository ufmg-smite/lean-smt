import Std
import Init.Data.String.Basic
import Mathlib
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Raw
import CompPoly

open Std CompPoly Lean

def matchStrWithRat (num : String) : ℚ :=
  let (isNegative, cleanNum) := if num.startsWith "-" then (true, num.drop 1) else (false, num)
  let result : ℚ :=
    if cleanNum.contains '/' then
      let parts := (cleanNum.split "/").toList
      let a := parts[0]!
      let b := parts[1]!
      let p := a.toNat?
      let q := b.toNat?
      match p, q with
      | some p', some q' => if q' ≠ 0 then p'/q' else 0
      | _, _ => 0
    else if cleanNum.contains '.' then
      let parts := (cleanNum.split ".").toList
      if parts[1]! == "0" then
        match parts[0]!.toNat? with
        | some n => n
        | none => 0
      else
        let m := 10 ^ parts[1]!.length
        let combined : String := parts[0]!.toString++parts[1]!.toString
        match combined.toNat? with
        | some n => n/m
        | none => 0
    else
      match cleanNum.toNat? with
      | some n => n
      | none => 0
  if isNegative then -result else result

def removeParentheses (s : String) : String :=
  if s.startsWith "(" && s.endsWith ")" then
    (s.drop 1 |>.dropEnd 1).toString
  else s

open CPolynomial Qq Lean
def getMonom (s: String) : Q(CPolynomial Rat) :=
  let l := (removeParentheses (s.trimAscii.toString)).splitOn "*"
  let coef : Rat := matchStrWithRat l[0]!
  let exp : Nat := if  !(s.contains "^") then if (l.length = 1) then 0 else 1 else ((s.splitOn "^").getLast!.trimAscii).toNat!
  let c : Q(CPolynomial Rat) := q(CPolynomial.C $coef)
  if exp = 0 ∨ coef = 0 then c else
    let pp: Q(CPolynomial Rat) := if exp = 1 then q(@CPolynomial.X Rat _ _ _ _) else
      mkApp2 q(@HPow.hPow (CPolynomial Rat) (ℕ) (CPolynomial Rat) _) q(@CPolynomial.X Rat _ _ _ _) q($exp)
    if coef = 1 then pp else
      let c : Q(CPolynomial Rat) := q(CPolynomial.C $coef)
      mkApp2 q(@HMul.hMul (CPolynomial Rat) (CPolynomial Rat) (CPolynomial Rat) _) c pp

def getPoly  (p: String): Q(CPolynomial Rat) := Id.run do
  let k : List String := p.splitOn "+"
  match k with
  | [] => return q(0)
  | h :: t =>
    let mut poly : Q(CPolynomial Rat) := getMonom h
    for monom in t do
      poly := mkApp2 q(@HAdd.hAdd (CPolynomial Rat) (CPolynomial Rat) (CPolynomial Rat) _) (getMonom monom) (poly)
    return poly

def getRaw (s:String) : Q(AlgebraicNumber.Raw) :=
  let t := ((s.drop 1).dropEnd 1).toString.splitOn ","
  let p: Q(CPolynomial Rat) := getPoly t[0]!
  let l : Rat := matchStrWithRat (t[1]!.trimAscii.drop 1).toString
  let r : Rat := matchStrWithRat (((t[2]!.dropEnd 1).trimAscii.toString))
  q(@AlgebraicNumber.Raw.mk $p $l $r)
