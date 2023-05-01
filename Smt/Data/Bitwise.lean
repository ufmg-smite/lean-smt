import Mathlib

infix:30 " ^^ " => xor

namespace Nat

#check Nat.binaryRec
#check bit_val
lemma bit_cases_on (n: Nat) : ∃ n', ∃ b', n = bit b' n' := by
  induction' n using Nat.binaryRec with b n''
  · use 0; use false; simp
  · use n''; use b

lemma bit_0 (b : Bool) : bit b 0 = b.toNat := by
  cases' b <;> simp

example (a b : Nat) (h: a < b ∨ a =b): a≤ b:= by exact le_of_lt_or_eq h


lemma bit_lt (h: bit b n < bit b' m) : n< m ∨ (n=m ∧ b = false ∧ b'= true)   := by 
  cases' b <;> cases' b' <;> simp [bit_val, cond] at *; assumption
  · apply lt_or_eq_of_le; by_contra' h1; linarith
  · by_contra' h1; linarith
  assumption

lemma bit_lt' (h: bit b n < bit b' m) (h1: ¬ (b = false ∧ b'= true)): n < m  := by 
  cases' b <;> cases' b' <;> simp [bit_val, cond] at * <;> linarith

-- MAKE THIS WORK
-- lemma bit_lt (h: bit b n < bit b' m) : cond (b = false ∧ b'= true) (n≤m) (n<m)  
-- cases' b <;> cases' b' <;> simp [bit_val, cond] at * <;> linarith

theorem lt_of_testbit2 (h: n<m) : ∃ i, Nat.testBit n i = false ∧ Nat.testBit m i = true ∧ ∀j, i <j → Nat.testBit m j = Nat.testBit n j := by
  revert m
  induction' n using Nat.binaryRec with b n ih
  <;> intro m
  · intro h
    have ⟨i, hi1, hi2⟩ := exists_most_significant_bit (show m ≠ 0 by linarith)
    use i
    simp [*]; assumption
  · intro h1
    have ⟨m', b', hbn⟩:= bit_cases_on m
    rw [hbn] at h1; rw [hbn]
    cases' bit_lt h1 with h3 h3
    · have ⟨i, iH⟩ := ih h3
      use Nat.succ i
      rw [testBit_succ, testBit_succ]
      exact ⟨iH.1, iH.2.1, by 
             intros j hj
             cases' j with j    
             · simp at hj
             · simp [testBit_succ, iH.2.2 j (Order.lt_of_succ_lt_succ hj)]⟩
    · use 0
      simp [testBit_zero]
      exact ⟨ h3.2.1, h3.2.2, by intros j hj
                                 have ⟨j' , hj⟩ := exists_eq_add_of_le' hj
                                 simp[hj,testBit_succ, h3.1]⟩ 

def bitwise_carry (x y : Nat) : Nat → Bool
  | 0     => false
  | i + 1 => (x.testBit i && y.testBit i) || ((x.testBit i ^^ y.testBit i) && bitwise_carry x y i)

def bitwise_add (x y z : Nat) : Nat → Nat
  | 0     => z.bit ((x.testBit 0 ^^ y.testBit 0) ^^ bitwise_carry 0 x y)
  | i + 1 =>
    bitwise_add x y (z.bit ((x.testBit (i + 1) ^^ y.testBit (i + 1)) ^^ bitwise_carry x y (i + 1))) i

theorem testBit_add {x y i: Nat} : (x + y).testBit i = ((x.testBit i ^^ y.testBit i) ^^ bitwise_carry x y i):= by sorry

theorem bitwise_add_eq_add (x y : Nat) : bitwise_add x y 0 i = (x + y) % 2 ^ (i + 1) := by sorry

def bitwise_not (x y : Nat) : Nat → Nat
  | 0     => y.bit !(x.testBit 0)
  | i + 1 => bitwise_not x (y.bit !(x.testBit (i + 1))) i

def bitwise_not' (x : Nat) : Nat → List Bool
  | 0     => [!(x.testBit 0)]
  | i + 1 => (!x.testBit (i+1)) :: bitwise_not' x i

def bitwise_neg (x i : Nat) : Nat := bitwise_add (bitwise_not x 0 i) 1 0 i

lemma bitwise_not_succ : bitwise_not x y i = bitwise_not x 0 i +2^(i+1)*y := by
  induction' i with i ih generalizing y
  · simp [bitwise_not, bit_val, add_comm]
  · simp only [bitwise_not]
    rw [ih, @ih (bit (!x.testBit (i+1)) 0)]
    simp [bit_val, mul_add,(show 2^(i+1)*(2*y) = 2^(succ (i+1))*y by rw [← mul_assoc]; aesop ), add_assoc, add_comm]
    
theorem testBit_eq_scale_pow_two {x w i:Nat} (h: i<w) : Nat.testBit x i = Nat.testBit (x+ 2^w* b) i := by sorry


theorem testBit_eq_scale_pow_two_bit {x w :Nat} {b:Bool} (h: x<2^w) : Nat.testBit (x+2^w*b.toNat) w = b:= by sorry


lemma testBit_not (h: i ≤ j): (bitwise_not x 0 j).testBit i = !x.testBit i := by
  induction' j with j ih generalizing i
  · simp at h; simp [h, bitwise_not]
  · simp only [bitwise_not]
    rw [bitwise_not_succ]
    cases' lt_or_eq_of_le h with h h
    · rw [← Nat.succ_eq_add_one, ← testBit_eq_scale_pow_two h, ih (SuccOrder.le_of_lt_succ h)]
    · simp only [bitwise_not, h]
      rw [bit_0, ← Nat.succ_eq_add_one, testBit_eq_scale_pow_two_bit (by sorry)]




@[simp] def toNat (bs : List Bool) : Nat :=
  toNat' (bs.length - 1) bs.reverse
where
  toNat' (e : Nat) : List Bool → Nat
    | [] => 0
    | b :: xs  => 2 ^ e*b.toNat + toNat' (e - 1) xs


theorem lt_pow_2_length {l : List Bool} (h:0< l.length) : toNat.toNat' (l.length-1) l < 2^(l.length) := by sorry

lemma list_rec_length {α : Type} {w: Nat} (f: Nat → List α)  (g: Nat → α)  (h0: f 0 = [g 0]) (h : ∀ n, f (n+1) = g (n+1) :: f n) : (f w).length = w+1 := by sorry

lemma list_rec_size {α : Type} {w: Nat} {f: Nat → List Bool}  {g: Nat → Bool}  {h0: f 0 = [g 0]} (h : ∀ n, f (n+1) = g (n+1) :: f n) : toNat.toNat' (w) (f w) < 2^(w+1) := by sorry

lemma list_rec_reverse {α : Type} (w: Nat) (f: Nat → List α) (h2 : i < (f w).length) (g: Nat → α)  (h0: f 0 = [g 0]) (h : ∀ n, f (n+1) = g (n+1) :: f n) : (f w)[i] = g ((f w).length - (i+1)) := by sorry

#check eq_zero_or_pos

theorem toNat_equiv_testBit (l: List Bool) (h: 0<l.length) (h1: i< l.length) : Nat.testBit (toNat.toNat' (l.length - 1) l) i = l[l.length - (i+1)]'(tsub_lt_self h (Nat.succ_pos i)) := by 
  induction' l with b l ih generalizing i
  · simp at h
  · simp only [toNat.toNat']
    cases' eq_zero_or_pos l.length with h0 h0
    · sorry
    · have h2: i ≤ l.length :=by sorry
      cases' lt_or_eq_of_le h2 with h3 h3
      · rw [add_comm, ← testBit_eq_scale_pow_two (by sorry), (show List.length (b :: l) - 1 - 1 = List.length l - 1 by simp), ih h0 h3]
        simp only [(show List.length (b :: l) - (i + 1) = List.length l - (i + 1) + 1 by sorry), List.cons_getElem_succ]
      · simp only [bitwise_not, h]
        rw [add_comm, (show (b :: l).length - 1 = l.length by simp), ← h3, testBit_eq_scale_pow_two_bit (by sorry)]
        simp [List.length_cons, h3]


example (a b c: Nat) (h: a < b): a+1 ≤ b := by exact h

#check Nat.succ_le_of_lt

@[simp] lemma tsub_tsub_eq_tsub_tsub {a b c : Nat} (h: c ≤  b) (h1:b ≤  a) : a-(b-c) = a-b + c:= by sorry

theorem list_rec_testBit (w: Nat) (f: Nat → List Bool) (h2 : i < (f w).length) (g: Nat → Bool)  (h0: f 0 = [g 0]) (h : ∀ n, f (n+1) = g (n+1) :: f n) : Nat.testBit (toNat.toNat' ((f w).length - 1) (f w)) i = g (i) := by
  rw [toNat_equiv_testBit (f w) (pos_of_gt h2) h2, list_rec_reverse w f (tsub_lt_self (pos_of_gt h2) (by simp)) g h0 h]
  rw [tsub_add_eq_tsub_tsub, tsub_tsub_eq_tsub_tsub (succ_le_of_lt h2) (show (f w).length ≤ (f w).length by rfl)]
  simp
  

  



    
#eval Nat.testBit 10 0

lemma testBit_not' (h: i ≤ j): (toNat.toNat' j (bitwise_not' x j)).testBit i = !x.testBit i := by sorry
  

    

#check Nat.sub_sub
#check testBit_zero

#check tsub_add_eq_add_tsub

example : 1 ≤ 2^i := by exact one_le_pow' i 1
example : 2^(succ i) = 2*2^i := by exact pow_succ'' i 2

example (h: 1 ≤ b)(h2: c ≤ d): c ≤ d*b := by exact le_mul_of_le_of_one_le h2 h

lemma bits_pow_two_minus_one (h: j ≤  i): testBit (2^(i+1) -1) j = true:= by
  induction' i with i ih generalizing j 
  · simp at h; simp [h]
  · have h1: 2^(succ i +1) -1 =  bit true (2^(i+1) -1) := by
      simp only [bit_val, cond]
      rw [Nat.mul_sub_left_distrib, mul_comm, ← pow_succ, mul_one]
      rw [← AddLECancellable.tsub_tsub_assoc (by simp; intros b c hb; linarith) (by rw [pow_succ'']; exact le_mul_of_le_of_one_le (by simp) (one_le_pow' (i+1) 1) ) (by simp)]
    rw[h1]
    cases' j with j j
    · rw[testBit_zero]
    · rw[testBit_succ, ih (le_of_succ_le_succ h)]


#eval testBit 10 4
#check pow_le_pow_of_le_right
#check lt_of_le_of_lt
#check sub_lt
example (h: 0<  a) (h1: 0 < 1) : a-1< a:= by exact tsub_lt_self h h1


lemma pow_two_succ (n: Nat) : 2^(n+1) = 2^n +2^n := by simp [Nat.pow_succ, Nat.mul_two]

-- This is now proved alot faster with shiftr_eq_div_pow but can also be proven by exists_most_significant_bit which is alot longer. Make that proof now shorter
example (a b : Nat) (h: a < b) : a+c < b+c := by exact add_lt_add_right h c
example : 2^(a+1) = 2*2^a := by exact pow_succ'' a 2
#check pow_pos

theorem bitwise_not_lt : bitwise_not x 0 i < 2^(i+1) := by
  induction' i with i ih
  · cases' h: testBit x 0 <;> simp [bitwise_not, bit_0, h]
  · unfold bitwise_not
    cases' h: testBit x (i+1) <;> simp [bitwise_not, bit_val, h]
    · rw [bitwise_not_succ, pow_two_succ (succ i), mul_one]
      exact add_lt_add_right ih (2^(i+1))
    · exact lt_trans ih (by simp[pow_succ'' (succ i), lt_mul_left])

theorem lt_pow_two_testBit_false (h: x < 2^i) (h1: i ≤ j) : x.testBit j = false:= by 
  simp [testBit, shiftr_eq_div_pow, Nat.div_eq_zero (lt_of_lt_of_le h (pow_le_pow_of_le_right (by simp) h1))]


#check lt_succ_self
#check lt_of_le_of_lt

example (a b c d: Nat) (h: a ≤ b)  : 0 ≠  2^a := by exact NeZero.ne' (2 ^ a)
example (h: a < b+1) : a ≤ b := by exact SuccOrder.le_of_lt_succ h
example (a b c d: Nat) (h: a<b) (h1: c<d): a+c < b+d := act_rel_act_of_rel_of_rel h h1

#eval bitwise_not 15 0 3
#eval testBit 15 3
#check pred_lt'
#check pow_pos

--   cases' le_or_gt j i with h h
--   rw [bits_pow_two_minus_one h, testBit_add, testBit_not (by linarith)]

lemma eq_of_testBit_eq_bounded (h0: x < 2^i) (h1: y< 2^i) (h: ∀ (j : Nat), j < i → x.testBit j = y.testBit j): x = y := by
  apply eq_of_testBit_eq
  intro k
  cases' lt_or_ge k i with h2 h2
  · exact h k h2
  · simp [lt_pow_two_testBit_false _ h2, *]

theorem bitwise_not_eq_neg_sub_one (h0: x <  2^(i+1)) : 
  bitwise_not x 0 i  + x  = 2 ^(i+1) -1 := by 
  have : bitwise_not x 0 i + x < 2^(i+2) := by
    rw [show 2^(i+2)= 2^(i+1) + 2^(i+1) by simp[pow_two_succ]]
    exact add_lt_add (bitwise_not_lt) h0
  have H: 2^(i+1) - 1 < 2^(i+2) := lt_trans (pred_lt (by simp[NeZero.ne, sub_zero])) (by simp[pow_succ'', lt_mul_left])
  apply eq_of_testBit_eq_bounded (this) H
  intros j hj1
  induction' j with j hj
  · rw [bits_pow_two_minus_one (by simp), testBit_add, testBit_not (by simp)]
    simp [bitwise_not, bitwise_carry]
  · replace hj:= hj (lt_trans (lt_succ_self j) hj1)
    have h3 := succ_le_succ_iff.mp (le_of_lt_succ hj1)
    cases' lt_or_eq_of_le (Nat.le_pred_of_lt hj1) with h h
    <;> rw [show i+2-1 = i+1 by simp] at h
    <;> rw [bits_pow_two_minus_one h3, testBit_add, testBit_not h3] at *
    · rw [bits_pow_two_minus_one (le_of_lt_succ h), testBit_not (le_of_lt_succ h)] 
      simpa [bitwise_carry, h3, testBit_not] using hj 
    · rw [lt_pow_two_testBit_false (sub_lt (pow_pos (by simp) (i+1)) (by simp)) (by simp[h])]
      have h4 := lt_pow_two_testBit_false h0 (show i+1 ≤ succ j by simp[h])
      have h5 := lt_pow_two_testBit_false (@bitwise_not_lt x i) (show i+1 ≤ succ j by simp[h])
      simpa [bitwise_carry, h4, h5, testBit_not h3] using hj



example (a b : Nat) (h: b ≤ a) : a+b+c = a+c+b := by exact add_right_comm a b c

lemma sub_both_sides {a b c : Nat} (h: c≤ b) (h1: a = b-c):  a +c = b:= 
  by rw [h1]; exact tsub_add_cancel_of_le h


lemma sub_both_sides' {a b c : Nat} (h1: a+c=b): a=b-c := 
  by rw [← h1]; simp


example (a: Nat): 1≤ 2^a := by exact one_le_pow' a 1


theorem bitwise_neg_eq_neg (x i : Nat) (h: x < 2^(i+1)) :
  bitwise_neg x i  = (2 ^ (i + 1) - x) % 2 ^ (i + 1) := by
  unfold bitwise_neg
  rw [bitwise_add_eq_add]
  apply congrArg (λ (x : Nat) => x % 2 ^ (i + 1))
  apply sub_both_sides'
  rw [add_right_comm]
  apply sub_both_sides (by simp[one_le_pow'])
  rw [← bitwise_not_eq_neg_sub_one h]



def bitwise_mul.sh (x y i j : Nat) : Bool :=
  if j ≤ i then
    x.testBit (i - j) ∧ y.testBit j
  else
    false

mutual
def bitwise_mul.res (x y : Nat) : Nat → Nat → Bool
  | i, 0     => sh x y i 0
  | 0, j     => sh x y 0 0
  | i, j + 1 =>
    ((res x y i j) ^^ (sh x y i (j + 1))) ^^ carry x y i (j + 1)

def bitwise_mul.carry (x y : Nat) : Nat → Nat → Bool
  | 0, j          => false
  | i, 0          => false  -- unreachable
  | i + 1, j + 1  =>
    if j < i then
      res x y i j ∧ sh x y i (j + 1) ∨ (res x y i j ∨ sh x y i (j + 1)) ∧ carry x y i (j + 1)
    else
      false
end
termination_by
  bitwise_mul.res x y i j   => i + j
  bitwise_mul.carry _ _ i j => i + j
decreasing_by
  simp_wf <;> try simp_arith <;> sorry

def bitwise_mul (x y n : Nat) : Nat := go x y 0 (n - 1)
where
  go (x y z : Nat) : Nat → Nat
  | 0     => z.bit (bitwise_mul.res x y 0 (n - 1))
  | i + 1 => go x y (z.bit (bitwise_mul.res x y (i + 1) (n - 1))) i

#eval bitwise_mul 2 3 3
#eval bit false 10

#eval bitwise_mul.res 2 3 1 2
#eval bitwise_mul.carry 2 3 0 2


theorem bitwise_mul_eq_mul' (x y n : Nat) (hx: x < 2^n) (hy : y <2^n) : bitwise_mul x y (2 * n) = x * y:= by
  sorry


#eval bitwise_mul 9 9 8

#eval bitwise_mul 127 127 7
#eval (127*127)%128


theorem bitwise_mul_eq_mul (x y n : Nat) : bitwise_mul x y n = (x * y) % 2 ^ n := by
  rw [mul_mod]
  rw [← bitwise_mul_eq_mul' (x % 2 ^ n) (y % 2 ^ n) n (sorry) (sorry)]
  sorry
  
  



--  0     => z.bit ((x.testBit 0 ^^ y.testBit 0) ^^ bitwise_carry 0 x y)
--   | i + 1 =>
--     bitwise_add x y (z.bit ((x.testBit (i + 1) ^^ y.testBit (i + 1)) ^^ bitwise_carry x y (i + 1))) i


end Nat
