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
lemma pow_two_succ (n: Nat) : 2^(n+1) = 2^n +2^n := by simp [Nat.pow_succ, Nat.mul_two]

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

theorem rec_succ (f : Nat → Nat → Nat) (g: Nat → Bool) (h0: ∀ y, f y 0 = y.bit (g 0) )(h: ∀y n, f y (n+1) = f (y.bit (g (n+1))) n) :  f y i = f 0 i +2^(i+1)*y := by
  induction' i with i ih generalizing y
  · simp [bit_val, h0, add_comm]
  · simp only [h]
    rw [ih, @ih (bit (g (i+1)) 0)]
    simp [bit_val, mul_add,(show 2^(i+1)*(2*y) = 2^(succ (i+1))*y by rw [← mul_assoc]; aesop ), add_assoc, add_comm]
    
lemma bitwise_not_succ : bitwise_not x y i = bitwise_not x 0 i +2^(i+1)*y := rec_succ (bitwise_not x) (λ i => !(x.testBit i)) (by simp[bitwise_not]) (by simp[bitwise_not])

theorem testBit_eq_scale_pow_two {x w i:Nat} (h: i<w) : Nat.testBit x i = Nat.testBit (x+ 2^w* b) i := by sorry

theorem testBit_eq_scale_pow_two' {x w i:Nat} (h: i<w) : Nat.testBit x i = Nat.testBit (2^w* b + x) i := by sorry
theorem testBit_eq_scale_pow_two'' {x w i:Nat} (h: i<w) : Nat.testBit x i = Nat.testBit (2^w+ x) i := by sorry

theorem testBit_eq_scale_pow_two_bit {x w :Nat} (b:Bool) (h: x<2^w) : Nat.testBit (x+2^w*b.toNat) w = b:= by sorry
theorem testBit_eq_scale_pow_two_bit' {x w :Nat} {b:Bool} (h: x<2^w) : Nat.testBit (2^w*b.toNat+x) w = b:= by sorry

theorem testBit_eq_scale_pow_two_bit'' {x w :Nat} (h: x<2^w) : Nat.testBit (2^w+x) w = true:= by sorry


theorem helper_2 (x i : Nat) : x % 2 ^ (i + 1) = 2^i * (Nat.testBit x i).toNat + x%(2^i) := by sorry

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
        rw [add_comm, (show (b :: l).length - 1 = l.length by simp), ← h3, testBit_eq_scale_pow_two_bit _ (by sorry)]
        simp [List.length_cons, h3]


example (a b c: Nat) (h: a < b): a+1 ≤ b := by exact h

#check Nat.succ_le_of_lt

@[simp] lemma tsub_tsub_eq_tsub_tsub {a b c : Nat} (h: c ≤  b) (h1:b ≤  a) : a-(b-c) = a-b + c:= by sorry



theorem list_rec_testBit (w: Nat) (f: Nat → List Bool) (h2 : i < (f w).length) (g: Nat → Bool)  (h0: f 0 = [g 0]) (h : ∀ n, f (n+1) = g (n+1) :: f n) : Nat.testBit (toNat.toNat' ((f w).length - 1) (f w)) i = g (i) := by
  rw [toNat_equiv_testBit (f w) (pos_of_gt h2) h2, list_rec_reverse w f (tsub_lt_self (pos_of_gt h2) (by simp)) g h0 h]
  rw [tsub_add_eq_tsub_tsub, tsub_tsub_eq_tsub_tsub (succ_le_of_lt h2) (show (f w).length ≤ (f w).length by rfl)]
  simp

theorem rec_size (f: Nat → Nat → Nat) (g: Nat → Bool) (h0: ∀ y, f y 0 = y.bit (g 0) )(h: ∀y n, f y (n+1) = f (y.bit (g (n+1))) n) : f 0 j < 2^(j+1) := by
  induction' j with j ih
  · simp [h0]
    cases' g 0 <;> simp
  · rw[h, rec_succ f g h0 h]
    cases' (g (j+1)) <;> simp [ih, pow_two_succ] at * <;> linarith


theorem rec_testBit (f: Nat → Nat → Nat) (g: Nat → Bool) (h0: ∀ y, f y 0 = y.bit (g 0) )(h: ∀y n, f y (n+1) = f (y.bit (g (n+1))) n) (h1: i≤ j) : (f 0 j).testBit i = g i := by
  induction' j with j ih generalizing i
  · simp at h1; rw [h0, h1, testBit_zero]
  · cases' lt_or_eq_of_le h1 with h1 h1
    · rw [h, ← ih (show i ≤ j by linarith), rec_succ f g h0 h, add_comm]
      simp [←testBit_eq_scale_pow_two' h1]
    · rw [h1, h, rec_succ f g h0 h]
      rw [show bit (g (j+1)) 0 = (g (j+1)).toNat by cases' g (j+1) <;> simp]
      rw [testBit_eq_scale_pow_two_bit (g (j+1)) (rec_size f g h0 h)]


lemma testBit_not (h: i ≤ j): (bitwise_not x 0 j).testBit i = !x.testBit i := rec_testBit (bitwise_not x) (λ i => !x.testBit i) (by simp[bitwise_not]) (by simp[bitwise_not]) h


    

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




-- This is now proved alot faster with shiftr_eq_div_pow but can also be proven by exists_most_significant_bit which is alot longer. Make that proof now shorter
example (a b : Nat) (h: a < b) : a+c < b+c := by exact add_lt_add_right h c
example : 2^(a+1) = 2*2^a := by exact pow_succ'' a 2
#check pow_pos

theorem bitwise_not_lt : bitwise_not x 0 i < 2^(i+1) := rec_size (bitwise_not x) (λ i => !x.testBit i) (by simp[bitwise_not]) (by simp[bitwise_not])

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

-- (x.testBit i && y.testBit i) || ((x.testBit i ^^ y.testBit i) && bitwise_carry x y i)

def bitwise_mul.carry (x y : Nat) : Nat → Nat → Bool
  | i, 0          => false -- unreachable
  | 0, j          => false 
  | i + 1, j + 1  =>
    if j < i then
      (res x y i j && sh x y i (j + 1)) || ((res x y i j ^^ sh x y i (j + 1))) && carry x y i (j + 1)
    else
      false
end
termination_by
  bitwise_mul.res x y i j   => i + j + 1
  bitwise_mul.carry _ _ i j => i + j



lemma bitwise_mul_res_zero : bitwise_mul.res x y 0 n = bitwise_mul.sh x y 0 0:= by
  cases' n <;> simp [bitwise_mul.res, bitwise_mul.sh]
  
lemma bitwise_mul_carry_zero : bitwise_mul.carry x y 0 n = false:= by
  cases' n <;> simp [bitwise_mul.carry]



def bitwise_mul (x y n : Nat) : Nat := go x y 0 (n - 1)
where
  go (x y z : Nat) : Nat → Nat
  | 0     => z.bit (bitwise_mul.res x y 0 (n - 1))
  | i + 1 => go x y (z.bit (bitwise_mul.res x y (i + 1) (n - 1))) i


-- def bitwise_mul' (x y n: Nat) : Nat → List Bool
--   | 0 => [bitwise_mul.res x y 0 (n - 1)]
--   | i + 1 => bitwise_mul.res x y (i+1) (n-1) :: bitwise_mul' x y n i

#eval bitwise_mul 2 3 3
#eval bit false 10
#eval bitwise_mul.res 2 3 1 2
#eval bitwise_mul.carry 2 3 0 2

def toBool' (x w: Nat) :=
  (go (w - 1)).reverse
where
  go (i : Nat) : List Bool := match i with
    | 0 => [Nat.testBit x 0]
    | i + 1 =>
      Nat.testBit x (i+1) :: go i



#check Nat.sub

example (a b : Nat): a-b ≤ a := by simp




  
  

-- theorem res_scale_pow_two (h: i< w) : bitwise_mul.res (2^w + x) y i j = bitwise_mul.res x y i j ∧ bitwise_mul.carry (2^w + x) y i j = bitwise_mul.carry x y i j := by
--   have ⟨k, hk⟩ : (∃ k : Nat, k = i+j) := by use (i+j)
--   induction' k using Nat.strongInductionOn with k ih generalizing i j
--   cases' k with k
--   · replace hk := eq_zero_of_add_eq_zero (Eq.symm hk) 
--     simp [hk, bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh]
--     rw [← testBit_eq_scale_pow_two'' (zero_lt_of_lt h)]
--   · cases' i with i <;> cases' j with j 
--     rotate_left 3
--     · have H: i<w  := by linarith
--       have H2: k = succ i + j  ∧ k = i + succ j := ⟨by linarith, by linarith⟩
--       by_cases hij: j + 1< succ i
--       · have hi1 : j < i := by linarith
--         have hi2: j+1 ≤ i := by linarith
--         have hi3: j+1 ≤ succ i := by linarith
--         simp [bitwise_mul.res, bitwise_mul.carry, hij, hi1, hi2, hi3, bitwise_mul.sh, ih k _ H H2.2, ih k _ h H2.1]
--         have h10: i-j< w ∧ i-(j+1)< w := by 
--           simp[lt_of_le_of_lt (show i -j≤ i by simp) H, lt_of_le_of_lt (show i- (j+1) ≤ i by simp) H]
--         simp [ih (k-1) (by simp_arith) (show i < w by linarith) (show k-1 = i+j by aesop)]
--         simp [← testBit_eq_scale_pow_two'', h10]
--       · have hi1 : ¬ j < i := by linarith
--         have hi2: ¬ j+1 ≤ i := by linarith
--         have hi3: ¬ j+1 ≤ succ i ∨ succ i = j+1 := by push_neg at *; exact lt_or_eq_of_le hij
--         cases'  hi3 with hi3 hi3
--         <;> simp [bitwise_mul.res, bitwise_mul.carry,  hi3,hi1, hi2, bitwise_mul.sh]
--         · simp [ih k _ H H2.2, ih k _ h H2.1]
--         · simp [← testBit_eq_scale_pow_two'' (zero_lt_of_lt h), ih k _ (hi3 ▸ h) (hi3 ▸ H2.1)]   
--     · simp [hk, bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh]
--       rw [← testBit_eq_scale_pow_two'' (by assumption)]
--     · simp [hk, bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh]
--       rw [← testBit_eq_scale_pow_two'' (by assumption)]
--     · simp [hk, bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh]
--       rw [← testBit_eq_scale_pow_two'' (by assumption)]
  
#check Or.inl



theorem res_scale_pow_two_new (h: i < w ∨ j< w) : bitwise_mul.res x (2^w+y) i j = bitwise_mul.res x y i j ∧ bitwise_mul.carry x (2^w+y) i j = bitwise_mul.carry x y i j := by
  have ⟨k, hk⟩ : (∃ k : Nat, k = i+j) := by use (i+j)
  induction' k using Nat.strongInductionOn with k ih generalizing i j
  cases' k with k
  · replace hk := eq_zero_of_add_eq_zero (Eq.symm hk) 
    simp [hk, bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh]
    rw [← testBit_eq_scale_pow_two'' (by cases' h <;> linarith)]
  · cases' i with i <;> cases' j with j 
    rotate_left 3
    · have H2: k = succ i + j  ∧ k = i + succ j := ⟨by linarith, by linarith⟩
      by_cases hij: j + 1< succ i
      · have H: j < w ∧ succ j < w := by apply And.intro <;> cases' h <;> linarith
        have H3: j < i ∧ j+1 ≤ i ∧ j+1 ≤ succ i := ⟨by linarith, by linarith, by linarith⟩
        simp [bitwise_mul.res, bitwise_mul.carry, hij, H3, bitwise_mul.sh, ih k _ (Or.inr H.2) H2.2, ih k _ (Or.inr H.1) H2.1]
        simp [ih (k-1) (by simp_arith) (by right; linarith) (show k-1 = i+j by aesop)]
        simp [← testBit_eq_scale_pow_two'', H.2]
      · have H3 : ¬ j < i  ∧ ¬ j+1 ≤ i := ⟨by linarith, by linarith⟩
        have hi3: ¬ j+1 ≤ succ i ∨ succ i = j+1 := by push_neg at *; exact lt_or_eq_of_le hij
        have H: succ i < w ∧ i< w := by apply And.intro <;> cases' h <;> linarith
        cases'  hi3 with hi3 hi3
        <;> simp [bitwise_mul.res, bitwise_mul.carry,  hi3, H3, bitwise_mul.sh]
        · simp [ih k _ (Or.inl H.2) H2.2, ih k _ (Or.inl H.1) H2.1]
        · simp [← testBit_eq_scale_pow_two'' (hi3 ▸ H.1), ih k _ (Or.inl (hi3 ▸ H.1)) (hi3 ▸ H2.1)]   
    · simp [hk, bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh]
      rw [← testBit_eq_scale_pow_two'' (by cases' h <;> linarith)]
    · simp [hk, bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh]
      rw [← testBit_eq_scale_pow_two'' (by cases' h <;> linarith)]
    · simp [hk, bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh]
      rw [← testBit_eq_scale_pow_two'' (by cases' h <;> linarith)]
  

-- I found the theorem we need to formalize
-- ∀ n, res (x+2^w) y w n = res x y w n ⊕ y_0 ∧ sh (x+2^w) y w n = sh x y w n ∧ carry (x+2^w) y w n = carry x y w n
-- Prove this by induction on n+w. Base case is easy. Then just unfold the recurrence relation and use the induction hypothesis.
-- Then generalize even more...
-- ∀ n, res (2^w+x) y (w+j) n = res x y (w+j) n ⊕ y_j ⊕ bit_add_carry x y j ∧ sh (2^w+x) y w n = sh x y w n ∧ carry (2^w*b+x) y w n = ... 
#check lt_succ_self

-- theorem res_scale_pow_two_bit_base0 (h: x< 2^w)(h2: n < w): ((bitwise_mul.res (2^w+ x) y w n) = ((y.testBit 0) ^^ (bitwise_mul.res x y w n))) ∧  (bitwise_mul.carry (2^w+x) y w n= bitwise_mul.carry x y w n) := by
--   induction' n with n ih
--   · simp [bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh]
--     cases' h1:y.testBit 0 <;> simp [testBit_eq_scale_pow_two_bit'' h] ; sorry
--   · cases' w with w
--     · simp at h2 
--     · have H: n+1 ≤ succ w ∧ n+1 ≤ w ∧ n < w ∧ n < succ w:= ⟨by linarith, by linarith, by linarith, by linarith⟩
--       have h10: w -n < succ w ∧ w-(n+1) < succ w := by 
--         simp[lt_of_le_of_lt (show w -n≤ w by simp) (lt_succ_self w), lt_of_le_of_lt (show w- (n+1) ≤ w by simp) (lt_succ_self w)]
--       simp [bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh, H, ih H.2.2.2]
--       simp [res_scale_pow_two, H]
--       simp [ ← testBit_eq_scale_pow_two'', h10]


-- theorem scale_pow_two_bit_base_new (h2: n < w): ((bitwise_mul.res x (2^w+y) w n) = (bitwise_mul.res x y w n)) ∧  (bitwise_mul.carry x (2^w+y) w n= bitwise_mul.carry x y w n) := by
--   induction' n with n ih
--   · simp [bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh, ←testBit_eq_scale_pow_two'' h2] 
--   · cases' w with w
--     · simp at h2 
--     · have H: n+1 ≤ succ w ∧ n+1 ≤ w ∧ n < w ∧ n < succ w:= ⟨by linarith, by linarith, by linarith, by linarith⟩
--       simp [bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh, H]
--       simp [ih H.2.2.2, res_scale_pow_two_new, H, h2]
--       simp [← testBit_eq_scale_pow_two'', H, h2]

theorem scale_pow_two_bit_new (h: y< 2^w): ((bitwise_mul.res x (2^w+y) w w) = ((bitwise_mul.res x y w w) ^^ (x.testBit 0))) ∧  (bitwise_mul.carry x (2^w+y) w w= bitwise_mul.carry x y w w) := by
  cases' w with w
  · cases' h3 : y.testBit 0
    <;> simp [bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh, testBit_add, bitwise_carry, h3]
  · simp [bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh, res_scale_pow_two_new (Or.inr (lt_succ_self w)), testBit_eq_scale_pow_two_bit'' h, lt_pow_two_testBit_false h (show w+1 ≤ w+1 by simp)]

-- theorem res_scale_pow_two_bit_base2 (h: x< 2^w) (h2: w < n): ((bitwise_mul.res (2^w+ x) y w n) = ((y.testBit 0) ^^ (bitwise_mul.res x y w n))) ∧  (bitwise_mul.carry (2^w+x) y w n= bitwise_mul.carry x y w n) := by
--   cases' w with w
--   · rw [← succ_pred_eq_of_pos h2]
--     · cases' h3 : x.testBit 0
--       <;> simp [bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh, testBit_add, bitwise_carry, h3]
--   · induction' n with n ih
--     · simp at h2
--     · have H: ¬ n+1 ≤ w ∧ ¬ n+1 ≤ succ w ∧ ¬ n < w:= ⟨by linarith, by linarith, by linarith⟩
--       simp [bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh, H]
--       cases' lt_or_eq_of_le (le_of_lt_succ h2) with h3 h3
--       · simp [ih h3]
--       · rw [← h3, (res_scale_pow_two_bit_base1 h).1]


-- theorem scale_pow_two_bit_base2_new (h: y< 2^w) (h2: w < n): ((bitwise_mul.res x (2^w+y) w n) = ( (bitwise_mul.res x y w n) ^^ (x.testBit 0))) ∧  (bitwise_mul.carry x (2^w+y) w n= bitwise_mul.carry x y w n) := by
--   cases' w with w
--   · rw [← succ_pred_eq_of_pos h2]
--     · cases' h3 : y.testBit 0
--       <;> simp [bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh, testBit_add, bitwise_carry, h3]
--   · induction' n with n ih
--     · simp at h2
--     · have H: ¬ n+1 ≤ w ∧ ¬ n+1 ≤ succ w ∧ ¬ n < w:= ⟨by linarith, by linarith, by linarith⟩
--       simp [bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh, H]
--       cases' lt_or_eq_of_le (le_of_lt_succ h2) with h3 h3
--       · simp [ih h3]
--       · rw [← h3, (scale_pow_two_bit_base1_new h).1]

theorem res_n_eq_res_w (h: w ≤ n ): bitwise_mul.res x y w n = bitwise_mul.res x y w w:= by
  have ⟨k, hk⟩ := exists_eq_add_of_le h; clear h
  cases' w with w
  · simp [bitwise_mul_res_zero]
  · induction' k with k ih generalizing n
    · simp [hk]
    · have : succ (n-1) = n :=by rw[← pred_eq_sub_one, succ_pred_eq_of_pos (show 0< n by linarith)]
      have H: ¬ n-1+1 ≤ succ w ∧ ¬ n-1<w ∧ succ w ≤ n:= ⟨by linarith, by linarith, by linarith⟩
      rw [← this]
      simp [bitwise_mul.res, H, bitwise_mul.sh, bitwise_mul.carry, ih (show n-1 = succ w+k by aesop)]

theorem carry_n_eq_false (h: w < n ) (h0: y < 2^(w+1) ): bitwise_mul.carry x y m n = false:= by
  cases' n with n
  · simp [bitwise_mul.carry]
  · induction' m with m ih
    · simp [bitwise_mul_carry_zero]
    · simp [bitwise_mul.carry, ih, bitwise_mul.sh, lt_pow_two_testBit_false h0 (show w+1 ≤ succ n by linarith)]


#check Nat.sub_add_cancel

theorem res_n_eq_res_w' (h: w ≤ n) (h1: w ≤ i) (h0: y< 2^(w+1)): bitwise_mul.res x y i n = bitwise_mul.res x y i w := by
  cases' lt_or_eq_of_le h with h2 h2; clear h
  · have ⟨k, hk1, hk2⟩ :∃ k, n = w+k ∧ 0 < k := by use n-w; rw[add_comm]; simp [Nat.sub_add_cancel (le_of_lt h2), h2]
    have := lt_pow_two_testBit_false h0 (show w+1 ≤ succ (w+k) by linarith)
    cases' i with i
    · simp [hk1, bitwise_mul.res, bitwise_mul_res_zero, this]
    · induction' k with k ih generalizing n
      · simp at hk2
      · simp [hk1, add_succ, bitwise_mul.res, bitwise_mul.sh, bitwise_mul.carry]
        have H:= lt_pow_two_testBit_false h0 (show w+1 ≤ succ (w+k) by linarith)  
        simp [H, res_n_eq_res_w, carry_n_eq_false (show w < succ (w+k) by linarith) h0]
        cases' k with k
        · simp
        · simp [ih (show w < w+succ k by linarith) rfl (succ_pos k) H]
  · simp [h2]


theorem res_n_eq_res_w'' (x: Nat) (h: i < n) (h1: k ≤ m) (h0: y < 2^(i+1)): bitwise_mul.res x y k m = bitwise_mul.res x y k n := by
  cases' le_or_gt i k with h2 h2
  · rw [res_n_eq_res_w' (show i ≤ m by linarith) h2 h0, res_n_eq_res_w' (show i ≤ n by linarith) h2 h0]
  · rw [res_n_eq_res_w h1, res_n_eq_res_w (show k ≤ n by linarith)]


-- theorem scale_pow_two_bit_0 (h: y < 2^w): (bitwise_mul.res x (2^w+y) (w+j) w) = false  := by

--   induction' k using Nat.strongInductionOn with k ih generalizing j n
--   cases' k with k
--   · sorry
--   · cases' w with w <;> cases' n with n
--     rotate_left 3
--     · rw [succ_add] at *
--       have H: n + 1 ≤ succ (w + j) ∧ n <  w+j ∧ n+1 ≤ w+j:= ⟨ by linarith, by linarith, by linarith⟩ 
--       simp [bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh, H]
--       sorry
--     · sorry
--     · sorry
--     · sorry
  
#check Nat.cast_div_div_div_cancel_right



theorem mul_pow_two (h: j < i): testBit (x*2^i) j = false := by
  simp only [testBit, shiftr_eq_div_pow]
  have: x * 2 ^ i / 2 ^ j = 2 ^ (i-j)*x := by
    rw [Nat.div_eq_iff_eq_mul_right (pow_pos (show 0 < 2 by simp) j) (dvd_mul_of_dvd_right (pow_dvd_pow 2 (le_of_lt h)) x), ← mul_assoc, ← pow_add]
    rw [add_sub_of_le (le_of_lt h), mul_comm]
  have H: x * 2 ^ i / 2 ^ j % 2 = 0 := by
    rw [this, mod_eq_zero_of_dvd ((show 2^(succ 0) = 2 by simp) ▸ dvd_mul_of_dvd_left (pow_dvd_pow 2 (succ_le_iff.mpr (tsub_pos_of_lt h))) x)]
  cases' h1: bodd (x*2^i / 2^j) <;> simp [H, mod_two_of_bodd, h1] at *

theorem mul_pow_two_gen (h: i ≤ n) : testBit (x*2^i) n = testBit x (n-i) := by
  simp only [testBit, shiftr_eq_div_pow]
  nth_rewrite 1 [← Nat.sub_add_cancel h, pow_add, Nat.mul_div_mul_right _ _ (pow_pos (show 0 < 2 by simp) i)]; rfl


theorem helper_of_main (h0: 0<i) (H2: j < 2*n) (h2: i ≤ n) (h: ∀ k < 2*n, bitwise_mul.res x ( y % 2 ^ i) k n = testBit ( x * (y % 2 ^ i)) k ) (hij: j < i): bitwise_carry (x * 2 ^ i) (x * (y % 2 ^ i)) j = false := by 
  induction' j with j hj
  · simp [bitwise_carry]
  · simp [bitwise_carry, hj (by linarith) (by linarith), mul_pow_two (show j < i by linarith)]
  

theorem helper_of_main1 (h0: 0<i) (H2: j < 2*n) (h2: i ≤ n) (h: ∀ k < 2*n, bitwise_mul.res x ( y % 2 ^ i) k n = testBit ( x * (y % 2 ^ i)) k ) (h1: i ≤ j): bitwise_carry (x * 2 ^ i) (x * (y % 2 ^ i)) j = bitwise_mul.carry x (2 ^ i + y % 2 ^ i) j i := by
  have H: (y % (2^i)) < 2^i :=by simp [pow_pos (show 2>0 by simp), mod_lt]
  have ⟨i', hi'⟩ : ∃i', i =succ i' := by use pred i; simp [Nat.succ_pred_eq_of_pos h0]
  rw [hi'] at h1 H h h2 h0 ⊢
  induction' j with j hj
  · simp [bitwise_carry, bitwise_mul.carry]
  · -- here i'+1 ≤ j is used three times. just find the actual term
    cases' (lt_or_eq_of_le h1) with h1 h1
    · simp [bitwise_carry, bitwise_mul.carry, (succ_lt_succ_iff).mp h1]
      rw [Bool.and_comm]
      simp [bitwise_mul.sh, (show i'+1 ≤ j by linarith)]
      rw [(@res_scale_pow_two_new j (succ i') i' x (y % 2 ^ (succ i')) (Or.inr (by linarith))).1]
      have H3:= h j (show j < 2*n by linarith)
      rw [res_n_eq_res_w' (show i'≤ n by linarith) (show i' ≤ j by linarith) H] at H3
      rw [H3, hj (by linarith) (by linarith)]
      rw [mul_pow_two_gen (show succ i' ≤ j by linarith)]
      simp [testBit_eq_scale_pow_two_bit'' H, Bool.xor_comm]
    · simp [bitwise_carry, bitwise_mul.carry, h1, mul_pow_two (lt_succ_self j)]
      simp [helper_of_main (h1 ▸ h0) (show j < 2*n by linarith) (h1 ▸ h2) (h1 ▸ h) (lt_succ_self j)]



theorem helper_main (h0: 0<i) (H2: j < 2*n) (h2: i ≤ n) (h: ∀ k < 2*n, bitwise_mul.res x ( y % 2 ^ i) k n = testBit ( x * (y % 2 ^ i)) k ): bitwise_mul.res x (2 ^ i + y % 2 ^ i) j n = testBit (x * 2 ^ i + x * (y % 2 ^ i)) j:= by
  have H: (y % (2^i)) < 2^i :=by simp [pow_pos (show 2>0 by simp), mod_lt]
  have ⟨i', hi'⟩ : ∃i', i =succ i' := by use pred i; simp [Nat.succ_pred_eq_of_pos h0]
  rw [hi'] at H h h2 h0 ⊢
  rw [testBit_add]
  induction' j with j hj
  · simp [bitwise_mul_res_zero, bitwise_mul.sh, bitwise_carry, ← testBit_eq_scale_pow_two'', *] at * 
    simp [bitwise_mul_res_zero, bitwise_mul.sh, ← h 0 (by linarith), mul_pow_two]
  · cases' lt_trichotomy (succ j) (succ i') with h1 h1 
    · rw [(res_scale_pow_two_new (Or.inl h1)).1, h (succ j) H2, mul_pow_two h1]
      simp [mul_pow_two _, helper_of_main h0 H2 h2 h h1]
    · cases' h1 with h1 h1
      · rw [h1, ← h (succ i') (h1 ▸ H2), res_n_eq_res_w (by linarith)]
        rw [res_n_eq_res_w (show succ i' ≤  n by linarith), (scale_pow_two_bit_new H).1]
        simp[bitwise_carry, scale_pow_two_bit_new H, mul_pow_two]
        simp [(succ_inj').mp h1 ▸ helper_of_main h0 (lt_trans (lt_succ_self j) H2) h2 h (by linarith)]
        simp [mul_pow_two_gen, Bool.xor_comm] 
      · rw [res_n_eq_res_w' h2 (by linarith) (by simp[pow_two_succ (succ i'), H])]
        simp [bitwise_mul.res, bitwise_mul.sh, le_of_lt h1, lt_of_succ_lt_succ h1, (show i' +1 ≤ j by linarith), helper_of_main1 h0 H2 h2 h (by linarith)]
        rw [testBit_eq_scale_pow_two_bit'' H]
        rw [mul_pow_two_gen (le_of_lt h1)]
        rw [(@res_scale_pow_two_new (succ j) (succ i') i' x (y % 2 ^ (succ i')) (Or.inr (by linarith))).1]
        have H3:= h (succ j) H2
        rw [res_n_eq_res_w' (show i' ≤ n by linarith) (show i' ≤ succ j by linarith) H] at H3
        rw [H3]
        simp [mul_pow_two_gen (le_of_lt h1)]
        nth_rewrite 1 [← Bool.xor_assoc]
        rw [Bool.xor_comm (testBit (x * (y % 2 ^ succ i')) (succ j)) _, Bool.xor_assoc]
    
    

theorem res_zero: bitwise_mul.res x 0 i j = false ∧ bitwise_mul.carry x 0 i j = false:= by
  have ⟨k, hk⟩ : ∃ k, k = i+j := by use i+j
  induction' k using Nat.strongInductionOn with k ih generalizing i j
  cases' j with j <;> cases' i with i
  <;> simp [bitwise_mul.sh, bitwise_mul.res, bitwise_mul.carry]
  simp [ih (k-1) (sub_lt (show 0< k by linarith) one_pos) (show k-1 = i + succ j by simp[hk, succ_add]), ih (k-1) (sub_lt (show 0< k by linarith) one_pos) (show k-1 = succ i + j by simp [hk])]
  

theorem res_one : bitwise_mul.res x 1 i j = x.testBit i ∧ bitwise_mul.carry x 1 i j = false:= by
  have ⟨k, hk⟩ : ∃ k, k = i+j := by use i+j
  induction' k using Nat.strongInductionOn with k ih generalizing i j
  cases' j with j <;> cases' i with i
  <;> simp [bitwise_mul.sh, bitwise_mul.res, bitwise_mul.carry]
  simp [ih (k-1) (sub_lt (show 0< k by linarith) one_pos) (show k-1 = i + succ j by simp[hk, succ_add]), ih (k-1) (sub_lt (show 0< k by linarith) one_pos) (show k-1 = succ i + j by simp [hk]), (pow_zero 2) ▸ testBit_two_pow_of_ne (Ne.symm (succ_ne_zero j))]
 
-- bitwise_carry (x * 2 ^ succ i') (x * (y % 2 ^ succ i')) j = bitwise_mul.carry x (2 ^ succ i' + y % 2 ^ succ i') j (i' + 1))
      
#check lt_of_add_lt_of_nonneg_left
#eval bitwise_mul.res 5 7 5 2 
#check succ_inj'
lemma toBool'_length (x w : Nat) : (toBool'.go x w).length = w+1 := list_rec_length (toBool'.go x) (Nat.testBit x) (by simp[toBool'.go]) (by simp[toBool'.go])

#eval bitwise_mul 19 71 0

theorem bitwise_mul_size (h: 0 < n) : bitwise_mul x y n < 2^n := by
  rw [← Nat.sub_add_cancel h]
  simp [bitwise_mul, rec_size (bitwise_mul.go (n-1+1) x y) (λ v => bitwise_mul.res x y v (n-1)) (by simp[bitwise_mul.go]) (by simp[bitwise_mul.go])]

theorem bitwise_mul_testBit (h1: i< n) : (bitwise_mul x y n).testBit i = bitwise_mul.res x y i (n-1) := by
  simp [bitwise_mul]
  exact rec_testBit (bitwise_mul.go n x y) (λ v => bitwise_mul.res x y v (n-1)) (by simp[bitwise_mul.go]) (by simp[bitwise_mul.go]) (le_pred_of_lt h1)

#check pow_le_pow
  
theorem bitwise_mul_eq_mul' (y: Nat)  (h: i ≤ n) (h1: x < 2^n): bitwise_mul x (y%(2^i)) (2*n) = x * (y%(2^i)):= by
  cases' eq_zero_or_pos n with Hn Hn
  · simp [Hn] at h; simp [h, Hn, bitwise_mul, bitwise_mul.go, mod_one, res_zero]
  apply eq_of_testBit_eq_bounded (bitwise_mul_size (succ_mul_pos 1 Hn)) (by linarith [pow_add 2 i n, Nat.mul_lt_mul' (le_of_lt (mod_lt y (pow_pos (show 2>0 by simp) i))) h1 (pow_pos (show 2>0 by simp) i), (pow_le_pow (show 1 ≤ 2 by linarith) (show i+n ≤ succ 1 * n by linarith[h]))])
  have H: ∀i, (y % (2^i)) + 2^i < 2^(i+1) :=by simp [pow_pos (show 2>0 by simp), mod_lt, add_lt_add, pow_two_succ]
  intros j hj
  simp only [bitwise_mul]
  rw [rec_testBit (bitwise_mul.go (2*n) x (y % 2 ^ i)) (λ v => bitwise_mul.res x (y % 2 ^ i) v (2*n - 1)) (by simp[bitwise_mul.go]) (by simp[bitwise_mul.go]) (le_pred_of_lt hj)]
  induction' i with i ih generalizing j
  · simp[mod_one, res_zero]
  · rw [helper_2 y i]
    cases' h1:y.testBit i
    · simp [Bool.toNat, ih (by linarith) j hj]
    · simp only [Bool.toNat, cond, mul_one]
      rw [mul_add]
      cases' eq_zero_or_pos i with hi hi
      · simp [mod_one, hi, res_one] 
      · rw [← helper_main hi hj (by linarith) (by intros k hk; rw [← res_n_eq_res_w'' x (show i < n by linarith) (le_pred_of_lt hk) (lt_of_add_lt_of_nonneg_left (H i) (zero_le (2^i))), ih (by linarith) k hk])] -- this command is so long how to make it shorter?
        rw [res_n_eq_res_w'' x (show i < n by linarith) (le_pred_of_lt hj) (Nat.add_comm _ _ ▸ (H i))]
      



  -- induction' i with i ih
  -- · sorry
  -- · cases' h1: y.testBit i
  --   · simp [Bool.toNat, ih]
  --     sorry
  --   · simp only [Bool.toNat, cond, mul_one]
  --     apply eq_of_testBit_eq_bounded (show _ < 2^(2*n) by sorry) sorry
  --     intros j hj
  --     have : 2*n = (bitwise_mul' x (y % 2 ^ (succ i)) (n + 1) (2*n)).length -1:= by sorry
  --     nth_rewrite 1 [this]
  --     rw [list_rec_testBit (2*n) (bitwise_mul' x (y % 2 ^ (succ i)) (n+1)) sorry (λ k: Nat => bitwise_mul.res x (y% 2^(succ i)) k n) (by simp[bitwise_mul']) (by simp[bitwise_mul'])]
  --     rw [helper_2 y i, h1, (show true.toNat = 1 from rfl), mul_one, mul_add]
  --     cases' i with i
  --     · simp [mod_one, bitwise_mul.res]
  --       sorry
  --     · apply helper_main (succ_pos i) hj (by linarith)
  --       sorry


#check dvd_mul_of_dvd_left
#check le_of_lt_succ
#check Nat.div_eq_zero

theorem testBit_eq_mod_pow_two (h: j < n): x.testBit j = (x%(2^n)).testBit j := by
  simp only [testBit, shiftr_eq_div_pow]
  induction' n with n ih generalizing j
  · simp at h
  · have := (dvd_iff_mod_eq_zero (2 ^ j) (2^n * Bool.toNat (testBit x n))).1 (dvd_mul_of_dvd_left (pow_dvd_pow 2 (le_of_lt_succ h)) (Bool.toNat (testBit x n)))
    have h1:= pow_pos (show 0<2 by simp) j
    rw [helper_2, add_div h1, this, zero_add]
    simp [show ¬ 2^j ≤ x%2^n %2^j by simp[mod_lt (x%(2^n)) h1]]
    cases' lt_or_eq_of_le (le_of_lt_succ h) with h1 h1
    · have h2:= @mul_pow_two j n (Bool.toNat (testBit x n)) h1
      simp_rw [testBit, shiftr_eq_div_pow, Nat.mul_comm, h2, ih h1] at *
      aesop
    · rw [h1]
      cases' h2: bodd (x/2^n)
      <;> simp [Nat.div_eq_zero, testBit, h2, shiftr_eq_div_pow]

#check Eq.symm

theorem res_eq_of_testBit_eq (h: 0 < n) (hx: ∀ j < n, x.testBit j = z.testBit j) (hy: ∀ j < n, y.testBit j = w.testBit j) (hi : i< n) (hj : j< n): bitwise_mul.res x y i j = bitwise_mul.res z w i j ∧ bitwise_mul.carry x y i j = bitwise_mul.carry z w i j := by
  have ⟨k, hk⟩ : ∃ k, k = i+j := by use i+j
  induction' k using Nat.strongInductionOn with k ih generalizing i j
  cases' j with j <;> cases' i with i
  <;> simp [bitwise_mul.sh, bitwise_mul.res, bitwise_mul.carry, hx 0 h, hy 0 h, hx _ hi]
  have: i<n ∧ j<n := by apply And.intro <;> linarith
  rw [hx (i - (j+1)) (by linarith [sub_le _ _, this.1]), hy (j+1) hj, hx (i-j) (by linarith [sub_le _ _, this.1])]
  simp [ih (k-1) (sub_lt (show 0< k by linarith) one_pos) this.1 hj (show k-1 = i + succ j by simp[hk, succ_add]), ih (k-1) (sub_lt (show 0< k by linarith) one_pos) hi this.2 (show k-1 = succ i + j by simp [hk])]
  cases' eq_zero_or_pos k with hk1 hk1
  · replace hk:= hk.symm
    simp [hk1, add_eq_zero_iff] at hk
  · simp [ih (k-1 -1) (lt_of_le_of_lt (sub_le (k-1) 1) (sub_lt hk1 one_pos)) this.1 this.2 (by simp[hk])]
      



theorem bitwise_mul_eq_mul (h: 0 < n) : bitwise_mul x y n = (x*y)%2^n := by
  rw [mul_mod]
  rw [← bitwise_mul_eq_mul' y rfl.ge (by simp [mod_lt, pow_pos])]
  apply eq_of_testBit_eq_bounded (bitwise_mul_size h) (by simp [mod_lt, pow_pos])
  intros j hj
  rw [← testBit_eq_mod_pow_two hj, bitwise_mul_testBit hj, bitwise_mul_testBit (show j < 2*n by linarith)]
  rw [res_n_eq_res_w (le_pred_of_lt hj), res_n_eq_res_w (show j ≤ 2*n-1 by rw [show 2*n-1 = n + (n-1) by simp[(show 2 = 1+1 by simp), add_mul, Nat.add_sub_assoc h]]; exact le_of_lt (Nat.lt_add_right j n (n-1) hj))]
  rw [(res_eq_of_testBit_eq h (fun k hk => (testBit_eq_mod_pow_two hk).symm) (fun k hk => (testBit_eq_mod_pow_two hk).symm) hj hj).1]


    
#check pow_le_pow


theorem testBit_mul : (x*y).testBit i = bitwise_mul.res x y i i := by 
  have ⟨n, hn1, hn2, hi⟩: ∃ n, x < 2^n ∧ y < 2^n ∧ i< n := by
    set m:= max (max x y) (i+1); use m
    simp [lt_two_pow, lt_of_lt_of_le (lt_two_pow _) (pow_le_pow (by simp) (show x ≤ m by simp)), lt_of_lt_of_le (lt_two_pow _) (pow_le_pow (by simp) (show y ≤ m by simp))]
  rw [← mod_eq_of_lt hn2]
  rw [← bitwise_mul_eq_mul' y rfl.ge hn1, bitwise_mul_testBit (by linarith)]
  rw [res_n_eq_res_w (show i ≤ 2*n-1 by rw [show 2*n-1 = n + (n-1) by simp[(show 2 = 1+1 by simp), add_mul, Nat.add_sub_assoc (pos_of_gt hi)]]; exact le_of_lt (Nat.lt_add_right i n (n-1) hi))]


def bitwise_extract (x i j: Nat) : Nat := go x j 0 (i-j)
where
  go (x j z : Nat) : Nat → Nat
  | 0     => z.bit (x.testBit j)
  | i + 1 => go x j (z.bit (x.testBit (i+1+j))) i

lemma bitwise_extract_size: bitwise_extract x i j < 2^(i-j+1) := by
  simp [bitwise_extract, rec_size (bitwise_extract.go x j) (λ v => x.testBit (v+j)) (by simp[bitwise_extract.go]) (by simp[bitwise_extract.go])]

lemma testBit_extract (h: k ≤ i-j) : (bitwise_extract x i j).testBit k = x.testBit (k+j) := rec_testBit (bitwise_extract.go x j) (λ k => x.testBit (k+j)) (by simp[bitwise_extract.go, testBit_zero]) (by simp[bitwise_extract.go, testBit_succ]) h
  
theorem shiftr_eq_shiftRight: Nat.shiftr = Nat.shiftRight := by
  funext x y
  induction' y with y hy generalizing x
  <;> simp [Nat.shiftr, Nat.shiftRight, Nat.div2_val, *]

theorem bitwise_extract_eq_extract : bitwise_extract x i j = (x >>> j)%(2^(i-j+1)):= by
  apply eq_of_testBit_eq_bounded (bitwise_extract_size) (by simp [mod_lt, pow_pos])
  intros k hk
  rw [testBit_extract (by linarith), ← testBit_eq_mod_pow_two hk]
  simp [HShiftRight.hShiftRight, ShiftRight.shiftRight, ← shiftr_eq_shiftRight, testBit, shiftr_eq_div_pow, Nat.div_div_eq_div_mul, pow_add, mul_comm]


def bitwise_concat (x y n m: Nat) : Nat := go x y n 0 (n+m-1)
where
  go (x y n z: Nat) : Nat → Nat
  | 0     => z.bit (x.testBit 0)
  | i + 1 => if i+1 < n then go x y n (z.bit (x.testBit (i+1))) i else go x y n (z.bit (y.testBit (i+1-n))) i

lemma bitwise_concat_size (h: 0< n): bitwise_concat x y n m < 2^(n+m) := by
  rw [← Nat.sub_add_cancel (show 1 ≤ n+m by linarith)]
  simp [bitwise_concat, rec_size (bitwise_concat.go x y n) (λ v => if v < n then x.testBit v else y.testBit (v-n)) (by simp[bitwise_concat.go, h]) (by intros u v; by_cases h1: v+1 < n <;> simp[bitwise_concat.go, h1])]

lemma testBit_concat (h: 0< n) (h2: k ≤ n+m-1): (bitwise_concat x y n m).testBit k = if k < n then x.testBit k else y.testBit (k-n) := rec_testBit (bitwise_concat.go x y n) (λ v => if v < n then x.testBit v else y.testBit (v-n)) (by simp[bitwise_concat.go, h]) (by intros u v; by_cases h1: v+1 < n <;> simp[bitwise_concat.go, h1]) h2

#check bitCasesOn
-- theorem bitwise'_bit' {f : Bool → Bool → Bool} (h : f false false = true) (a m b n) :
--     bitwise' f (bit a m) (bit b n) = bit (f a b) (bitwise' f m n) := by
--   unfold bitwise'
--   rw [binaryRec_eq, binaryRec_eq]
--   · induction' ftf : f true false
--     rw [show f a false = !a by cases a <;> assumption]
--     nth_rewrite 5 [show 0 = bit !a 0 by cases' a <;> simp]
--     apply @congr_arg _ _ _ 0 (bit !a)
--     swap
--     rw [show f a false = true by cases a <;> assumption]
--     apply @congr_arg _ _ _ 0 (bit true)
--     all_goals
--     { apply bitCasesOn m
--       intro a m
--       rw [binaryRec_eq, binaryRec_zero]
--       · rfl
--       · rw [← bitwise'_bit_aux h, ftf] }
--   · exact bitwise'_bit_aux h


#reduce bitwise (λ (b b': Bool) => !(b && b')) 9 12
#reduce bitwise' (λ (b b': Bool) => !(b && b')) 9 12

#eval bitwise' (λ (b b': Bool) => !(b && b')) (bit false 1) (bit false 0) 
#eval bit ((λ (b b': Bool) => !(b && b')) false false) (bitwise' (λ (b b': Bool) => !(b && b')) 10 59)
#eval (λ (b b': Bool) => !(b && b')) false false
#eval bits 15

#check add_lt_add

lemma bitwise_eq_bitwise' (f: Bool → Bool → Bool ) (h: f false false = false): bitwise f = bitwise' f := by
  funext x y
  have ⟨k, hk⟩ : ∃ k, k = x+y := by use x+y
  induction' k using Nat.strongInductionOn with k ih generalizing x y
  by_cases h1: x= 0
  <;> by_cases h2: y= 0
  · unfold bitwise
    simp [h1, h2, h]
  · unfold bitwise bitwise' ; simp[h1]; aesop
  · unfold bitwise ; simp [h2]; aesop
  · rw [← bit_decomp x, ← bit_decomp y]
    unfold bitwise
    rw [bit_decomp, bit_decomp, mod_two_of_bodd, mod_two_of_bodd]
    nth_rewrite 8 [← bit_decomp x]
    nth_rewrite 8 [← bit_decomp y]
    rw [bitwise'_bit (show _ by simp[h])]
    cases' hx: bodd x
    <;> cases' hy: bodd y
    <;> ring_nf
    <;> simp [h1, h2, hx, hy, bit_val, div2_val, mul_comm, ih (div2 x + div2 y) (by rw [hk, div2_val, div2_val]; simp[add_lt_add (bitwise_rec_lemma h1) (bitwise_rec_lemma h2)]) (x/2) (y/2) (by simp[div2_val]), add_comm, h]
    <;> aesop


lemma or_eq_or': bitwise or = lor' := by 
  simp [bitwise_eq_bitwise' or (by simp), lor']
  

  
-- theorem or_le_add (x y : Nat) : x ||| y ≤ x+y := by
--   induction' x using Nat.binaryRec with b x hx
--   <;> induction' y using Nat.binaryRec with b' y hy
--   · simp
--   · sorry
--   · sorry
--   · cases' b with b b
--     <;> cases' b' with b' b'
--     <;> simp only [hx, HOr.hOr, OrOp.or, lor, bitwise_eq_bitwise']
--     <;> sorry
#check eq_of_testBit_eq

theorem bitwise_lt (hx : x < 2^n) (hy: y< 2^n) (h: f false false = false): bitwise f x y < 2^n := by
  rw [bitwise_eq_bitwise' f h]
  apply lt_of_testBit n (by simp[testBit_bitwise' h x y n, lt_pow_two_testBit_false hx rfl.le, lt_pow_two_testBit_false hy rfl.le, h]) (testBit_two_pow_self n)
  intro j hj
  rw[testBit_bitwise' h x y j, lt_pow_two_testBit_false hx (le_of_lt hj), lt_pow_two_testBit_false hy (le_of_lt hj), h, testBit_two_pow_of_ne (ne_of_lt hj)]

#check lt_pow_two_testBit_false
theorem bitwise_concat_eq_concat (h: 0< n) (hx : x < 2^n) (hy: y< 2^m): bitwise_concat x y n m = y <<< n ||| x := by
  have H: x < 2^(n+m) ∧ y*2^n < 2^(n+m):= by
    apply And.intro
    · exact lt_of_lt_of_le hx ((pow_add 2 n m).symm ▸ le_mul_of_one_le_right' (by linarith))
    · rw [pow_add, mul_comm]; simp[hy, mul_lt_mul_left (pow_pos (show 0 < 2 by simp) n)]
  apply eq_of_testBit_eq_bounded (bitwise_concat_size h) (by simp only [lor, shiftLeft_eq]; exact bitwise_lt H.2 H.1 rfl)
  intros k hk
  rw [testBit_concat h (Nat.le_pred_of_lt hk)]
  by_cases h1: k <n
  <;> simp only [h1, ge_iff_le, ite_true, ite_false, shiftLeft_eq, HOr.hOr, OrOp.or, lor, or_eq_or', lor']
  <;> rw [testBit_bitwise' (by simp)]
  · simp [mul_pow_two h1]
  · rw [mul_pow_two_gen (by linarith), lt_pow_two_testBit_false hx (by linarith)]; simp


  
def bitwise_eq (x y n: Nat) : Prop := go x y (n-1)
where
  go (x y : Nat) : Nat → Prop
  | 0     => x.testBit 0 == y.testBit 0
  | i + 1 => (x.testBit (i+1) == y.testBit (i+1)) ∧ go x y i
-- maybe jst use forall here?

theorem bitwise_eq_eq_forall (h: 0 < n): bitwise_eq x y n = ∀ j ≤ n-1, x.testBit j = y.testBit j := by
  apply propext;
  induction' n with n ih
  · simp at h
  · cases' n with n
    · simp [bitwise_eq, bitwise_eq.go, ih]
    · simp only [bitwise_eq, bitwise_eq.go, beq_iff_eq, ge_iff_le, succ_sub_succ_eq_sub, nonpos_iff_eq_zero,add_eq_zero, and_false, tsub_zero] at *
      rw [ih (by linarith)]; apply Iff.intro
      · intros H j hj
        cases' lt_or_eq_of_le hj with hj hj
        · simp [H, le_of_lt_succ hj]
        · simp [H, hj]
      · intro H
        exact ⟨H (n+1) rfl.le, fun j hj => H j (by linarith)⟩

theorem bitwise_eq_eq_iff (h: 0 < n) (hx : x < 2^n) (hy: y < 2^n ): (x = y) = bitwise_eq x y n := by
  rw [bitwise_eq_eq_forall h]
  apply propext; apply Iff.intro
  <;> intro H
  · simp[H]
  · apply eq_of_testBit_eq_bounded hx hy
    intro j hj
    exact H j (le_pred_of_lt hj)


theorem msb_ind (p : Nat → Prop) (h : p 0) (h' : ∀ w, p (x % 2 ^ w) → p (x % 2 ^ (w + 1))) : p x := by
  have : x< 2^x := lt_two_pow x
  rw [←mod_eq_of_lt this]
  suffices goal : ∀ i, i≤x → p (x % 2^i) by exact goal x rfl.le
  intro i hix
  induction' i with i ih
  · simp [mod_one, h]
  · simp [Bool.toNat, h' i, ih (by linarith)]


end Nat
