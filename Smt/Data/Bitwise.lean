import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.IntervalCases


infix:30 " ^^ " => xor

namespace Nat

/-! ### Preliminaries -/

lemma bit_toNat (b : Bool) : bit b 0 = b.toNat := by cases' b <;> simp

theorem two_pow_pos (w : Nat) : 0 < 2^w := Nat.pos_pow_of_pos _ (by decide)

theorem two_pow_succ (w : Nat) : 2^(w+1) = 2^w + 2^w := by simp [pow_succ, mul_two] --should be in mathlib

lemma lt_succ_two_pow {y b i : Nat} (h: b ≤ 1) (hy : y < 2^i) : 2^i * b + y < 2^(i+1) := by 
  rw [two_pow_succ]
  exact add_lt_add_of_le_of_lt (mul_le_of_le_one_right' h) hy

lemma toNat_le_one (b: Bool) : b.toNat ≤ 1 := by cases' b <;> simp

@[simp] lemma toNat_eq_bif {b: Bool}: cond b 1 0 = b.toNat := by simp [cond, Bool.toNat]

lemma shiftr_eq_testBit : Nat.shiftr x i %2 = (x.testBit i).toNat := by simp [Nat.testBit, Nat.mod_two_of_bodd]

lemma div_add_mod_two_pow (m n : Nat) : n = 2^m*Nat.shiftr n m + n%(2^m):= by simp_rw [Nat.shiftr_eq_div_pow, Nat.div_add_mod]

theorem mod_two_pow_succ (x i : Nat) : x % 2 ^ (i + 1) = 2^i * (Nat.testBit x i).toNat + x % (2^i):= by 
  have h1 := div_add_mod_two_pow i x
  rw [← div_add_mod (Nat.shiftr x i) 2, mul_add, ←mul_assoc, ←pow_succ, shiftr_eq_testBit] at h1
  have := lt_succ_two_pow (toNat_le_one (x.testBit i)) (mod_lt x (NeZero.pos (2^i)))
  simp [(Nat.div_mod_unique (two_pow_pos (i+1))).mpr ⟨add_rotate _ _ (x%(2^i)) ▸ h1.symm, this⟩]


theorem bodd_eq_mod_two : bodd x = bodd y ↔ x % 2 = y % 2 := by
  cases' hx : bodd x <;> cases' hy : bodd y 
  <;> simp [mod_two_of_bodd, hx ,hy]

-- x+2^w*b or 2^w*b+x or 2^w+x decide!
theorem testBit_translate {x w i:Nat} (h: i<w) : Nat.testBit x i = Nat.testBit (2^w* b + x) i := by
  simp only [testBit, shiftr_eq_div_pow, bodd_eq_mod_two]
  rw [Nat.add_div_of_dvd_right (by simp [Dvd.dvd.mul_right, pow_dvd_pow, le_of_lt h]), add_mod]
  have h1: (2^w/2^i)%2 = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero] -- can these two lines be combined or sth?
    use 2^(w-(i+1))
    rw [Nat.pow_div (by linarith) (by decide), mul_comm, ← pow_succ 2 _, succ_eq_add_one]
    simp [← Nat.sub_add_comm, succ_le_of_lt h]
  simp [mul_comm, Nat.mul_div_assoc b (pow_dvd_pow 2 (le_of_lt h)), mul_mod, h1]

theorem testBit_translate' {x w :Nat} {b:Bool} (h: x<2^w) : Nat.testBit (2^w*b.toNat + x) w = b:= by
  simp only [Nat.testBit, Nat.shiftr_eq_div_pow]
  rw [Nat.add_div_of_dvd_right (Dvd.intro _ rfl), Nat.div_eq_zero h, add_zero]
  cases' b <;> simp 

@[simp] lemma toNat_true : true.toNat = 1 := rfl

-- what to do with these?
theorem testBit_translate_one {x w i:Nat} (h: i<w) : Nat.testBit x i = Nat.testBit (2^w+ x) i := mul_one (2^w) ▸ (@testBit_translate 1 _ _ _ h)

theorem testBit_translate_one' {x w :Nat} (h: x<2^w) : Nat.testBit (2^w+x) w = true:= mul_one (2^w) ▸ toNat_true ▸ (@testBit_translate' x w true h)

@[simp] lemma testBit_bool : testBit b.toNat 0 = b := by cases' b <;> simp

-- maybe jst use foldr or something?
-- unfold twice? that's annoying
def toNat (f : Nat → Bool) (z : Nat) : Nat → Nat
  | 0 => z
  | i + 1 => toNat f (z.bit (f i)) i

def toNat' (bs : List Bool) : Nat := List.foldr Nat.bit 0 bs

#eval (toNat' [false, true, false, true]).testBit 4

theorem toNat_succ {f : Nat → Bool}: toNat f z i = 2^i*z + toNat f 0 i:= by
  induction' i with i ih generalizing z
  · simp [toNat, bit_val]
  · simp only [toNat, @ih (bit (f i) 0), @ih (bit (f i) z)]
    rw [bit_val, mul_add, ← mul_assoc, ← pow_succ]
    simp [bit_val, add_assoc] 

theorem toNat_lt {f: Nat → Bool} : toNat f 0 i < 2^i := by
  induction' i with i ih
  · simp [toNat, bit_val, lt_succ, toNat_le_one]
  · simp only [toNat]
    rw [toNat_succ]
    cases' (f i) <;> simp [two_pow_succ, ih]; linarith -- freakin simp doesnt finish

theorem toNat_testBit {f: Nat → Bool} (h1: i < j) : (toNat f 0 j).testBit i = f i := by
  induction' j, (pos_of_gt h1) using Nat.le_induction with j _ ih generalizing i
  · simp [lt_one_iff.1 h1, toNat]
  · cases' lt_or_eq_of_le (lt_succ_iff.mp h1) with h1 h1
    · rw [← ih h1, toNat, toNat_succ, ←testBit_translate h1]
    · rw [h1, toNat, toNat_succ, bit_toNat, testBit_translate' (toNat_lt)]

theorem lt_two_pow_testBit_false (h: x < 2^i) (h1: i ≤ j) : x.testBit j = false:= by 
  simp [testBit, shiftr_eq_div_pow, Nat.div_eq_zero (lt_of_lt_of_le h (pow_le_pow_of_le_right (by decide) h1))]

theorem eq_of_testBit_eq_lt (h0: x < 2^i) (h1: y< 2^i) (h: ∀ (j : Nat), j < i → x.testBit j = y.testBit j): x = y := by
  apply eq_of_testBit_eq
  intro k
  apply Nat.lt_ge_by_cases (h k) (fun h2 => by simp [lt_two_pow_testBit_false _ h2, *]) -- how to combine this line with the previous one?


/-! ### Unsigned less than -/

lemma bit_lt (h: bit b n < bit b' m) : n < m ∨ (n = m ∧ b = false ∧ b'= true) := by 
  cases' b <;> cases' b' <;> revert h
  <;> simp [le_iff_lt_or_eq]

-- simp [*] at * should work! it almost does... ooh i found a trick with revert!
--also instead of cases' b <;> cases' b'?

def bitwise_ult (x y w : Nat) := go x y (w - 1) 
where
  go (x y : Nat) : Nat →  Prop
    | 0     => ¬ x.testBit 0  ∧ y.testBit 0
    | i + 1 => (¬ x.testBit (i + 1) ∧ y.testBit (i+1)) ∨ (¬(x.testBit (i + 1) ∧ ¬ y.testBit (i + 1)) ∧ go x y i)

theorem lt_of_testbit (h: n<m) : ∃ i, Nat.testBit n i = false ∧ Nat.testBit m i = true ∧ ∀j, i <j → Nat.testBit m j = Nat.testBit n j := by
  induction' n using Nat.binaryRec with b n ih generalizing m
  · have ⟨i, _, _⟩ := exists_most_significant_bit (ne_of_lt h).symm
    use i; simpa [*] --combine use and simp?
  · rw [← bit_decomp m] at h ⊢
    cases' bit_lt h with h3 h3
    · have ⟨i, iH⟩ := ih h3
      use Nat.succ i; simp only [testBit_succ]
      exact ⟨iH.1, iH.2.1, by 
             intros j hj; cases' j with j -- could use le_induction here but how. could these 4 lines be jst one simp?
             · simp at hj
             · simp [testBit_succ, iH.2.2 j (by linarith)]⟩
    · use 0; simp only [testBit_zero]
      exact ⟨ h3.2.1, h3.2.2, by intros j hj
                                 have ⟨j', hj⟩ := exists_eq_add_of_le' hj -- again, do we really need this?
                                 simp[hj, testBit_succ, h3.1]⟩ 

theorem testBit_true_lt_two_pow (h: x.testBit i = true) (hx : x < 2^w) : i < w := by
  by_contra'; simp [lt_two_pow_testBit_false hx this] at h
  -- could jst use mt (modus tollens?) but it trips on push_neg

theorem bitwise_ult_of_ult (hy: y< 2^w) (h1: x < y) : bitwise_ult x y w := by
  have ⟨i, hi1, hi2, hi3⟩ := lt_of_testbit h1
  suffices goal: ∀ j, i+1 ≤ j → bitwise_ult x y j from goal w (testBit_true_lt_two_pow hi2 hy)
  apply le_induction
  · cases' i <;> simp [bitwise_ult, bitwise_ult.go, hi1, hi2]
  · intros j hj ih
    have ⟨j', hj'⟩ := exists_eq_add_of_le' (le_of_add_le_right hj) -- why?
    simp only [bitwise_ult, bitwise_ult.go, hj', succ_sub_one j'] at ih ⊢ -- could make a lemma that descends on bitwise_ult or just make the inductive hyp on bitwise_ult.go
    simp [ih, hi3 (j'+1) (by linarith)]


/-! ### Addition -/

def bitwise_carry (x y : Nat) : Nat → Bool
  | 0     => false
  | i + 1 => (x.testBit i && y.testBit i) || ((x.testBit i ^^ y.testBit i) && bitwise_carry x y i)

@[simp] def bitwise_add (x y i: Nat) := toNat (λ j => (x.testBit j ^^ y.testBit j) ^^ bitwise_carry x y j) 0 i

lemma unfold_carry (x y i : Nat) : (bitwise_carry x y (i+1)).toNat = ((Nat.testBit x i && Nat.testBit y i) || ((Nat.testBit x i ^^ Nat.testBit y i) && bitwise_carry x y i)).toNat := by
  simp [bitwise_carry]
--do we really need this^

theorem bitwise_add_eq_add_base (x y i: Nat) : x%(2^i) + y%(2^i) = bitwise_add x y i + 2^i*(bitwise_carry x y i).toNat := by
  induction' i with i hi
  · simp [mod_one, toNat, bitwise_carry]
  · rw [mod_two_pow_succ x, mod_two_pow_succ y]
    rw [add_assoc, add_comm _ (y % 2 ^ i), ← add_assoc (x % 2 ^ i)]
    rw [hi, unfold_carry x y i, two_pow_succ i]
    cases' hx : Nat.testBit x i <;> cases' hy : Nat.testBit y i
    <;> cases' hc : bitwise_carry x y i
    <;> simp [Bool.toNat, @toNat_succ 1 i _, two_pow_succ, hx, hy, hc, toNat]
    <;> ring -- non terminal simp 

theorem bitwise_add_eq_add (x y : Nat) : bitwise_add x y i = (x + y) % 2 ^ i := by
  rw [Nat.add_mod, bitwise_add_eq_add_base]
  cases' i with i i
  · simp [mod_one, toNat]
  · simp [bitwise_add, Nat.mod_eq_of_lt toNat_lt]

#eval bitwise_add 10 9 5

theorem testBit_add {x y i: Nat} : (x + y).testBit i = ((x.testBit i ^^ y.testBit i) ^^ bitwise_carry x y i):= by
  have := lt_of_lt_of_le (lt_trans (lt_two_pow (x + y)) (pow_lt_pow_succ (by decide) (x + y))) (pow_le_pow_of_le_right (show 0 < 2 by decide) (@le_add_self _ _ _ i))
  rw [← Nat.mod_eq_of_lt this, ← add_assoc, ← bitwise_add_eq_add x y]
  simp [toNat_testBit (show i < i + (x + y) + 1 by linarith)]


/-! ### Negation -/

def bitwise_not (x i : Nat) : Nat := toNat (λ j => !x.testBit j) 0 i

def bitwise_neg (x i : Nat) : Nat := bitwise_add (bitwise_not x i) 1 i

lemma two_pow_succ_minus_one : 2^(i+1) - 1 = bit true (2^i-1) := by
  simp only [bit_val, cond]
  zify [two_pow_pos]
  rw [pow_succ'']; ring --sth can be removed here

lemma testBit_two_pow_minus_one (h0 : 0 < i) (h: j < i): testBit (2^i -1) j = true:= by
  induction' i, h0 using Nat.le_induction with i _ ih generalizing j 
  · simp [lt_one_iff.1 h]
  · rw [two_pow_succ_minus_one]
    cases' j with j
    · rw[testBit_zero]
    · rw[testBit_succ, ih (by linarith)]

lemma bitwise_carry_not_eq_false (h: j ≤ i) : bitwise_carry (toNat (fun j => !testBit x j) 0 i) x j = false := by
  induction' j with j ih
  · simp [bitwise_carry]
  · simp [bitwise_carry, ih (le_of_succ_le h), toNat_testBit (show j < i by linarith)]

--i tried shortening this proof by formalizing the lemma above. the last index is annoying.
theorem bitwise_not_eq_neg_sub_one (h0: x <  2^i) : bitwise_not x i  + x  = 2 ^ i - 1 := by 
  simp only [bitwise_not]
  apply eq_of_testBit_eq_lt ((two_pow_succ i).symm ▸ add_lt_add (toNat_lt) h0) (lt_trans (sub_lt (two_pow_pos _) (by decide)) (by simp [pow_lt_pow_succ]))
  intros j hj; cases' (lt_succ_iff_lt_or_eq.mp hj) with hj hj
  · rw [testBit_add, testBit_two_pow_minus_one (pos_of_gt hj) hj, toNat_testBit hj]
    simp [bitwise_carry_not_eq_false (le_of_lt hj)]
  · rw [testBit_add, lt_two_pow_testBit_false h0 (by linarith), lt_two_pow_testBit_false (toNat_lt) (by linarith)]
    rw [lt_two_pow_testBit_false (sub_lt (two_pow_pos i) (by simp)) (by simp [hj]), hj]
    simp [bitwise_carry, toNat_testBit, bitwise_carry_not_eq_false]

theorem bitwise_neg_eq_neg (h: x < 2^i) : bitwise_neg x i  = (2 ^ i - x) % 2 ^ i := by
  simp only [bitwise_neg, bitwise_add_eq_add]; congr
  have := bitwise_not_eq_neg_sub_one h
  zify [le_of_lt h, (one_le_of_lt (two_pow_pos i))] at * ; linarith

theorem rec_succ (f : Nat → Nat → Nat) (g: Nat → Bool) (h0: ∀ y, f y 0 = y.bit (g 0) )(h: ∀y n, f y (n+1) = f (y.bit (g (n+1))) n) :  f y i = 2^(i+1)*y + f 0 i := by
  induction' i with i ih generalizing y
  · simp [bit_val, h0, add_comm]
  · simp only [h]
    rw [ih, @ih (bit (g (i+1)) 0)]
    simp [bit_val, mul_add,(show 2^(i+1)*(2*y) = 2^(succ (i+1))*y by rw [← mul_assoc]; aesop ), add_assoc, add_comm]

theorem rec_size (f: Nat → Nat → Nat) (g: Nat → Bool) (h0: ∀ y, f y 0 = y.bit (g 0) )(h: ∀y n, f y (n+1) = f (y.bit (g (n+1))) n) : f 0 j < 2^(j+1) := by
  induction' j with j ih
  · simp [h0]
    cases' g 0 <;> simp
  · rw[h, rec_succ f g h0 h]
    cases' (g (j+1)) <;> simp [ih, two_pow_succ] at * <;> linarith

theorem rec_testBit {f: Nat → Nat → Nat} (g: Nat → Bool) (h0: ∀ y, f y 0 = y.bit (g 0) )(h: ∀y n, f y (n+1) = f (y.bit (g (n+1))) n) (h1: i≤ j) : (f 0 j).testBit i = g i := by
  induction' j with j ih generalizing i
  · simp at h1; rw [h0, h1, testBit_zero]
  · cases' lt_or_eq_of_le h1 with h1 h1
    · rw [h, ← ih (show i ≤ j by linarith), rec_succ f g h0 h, ←testBit_translate h1]
    · rw [h1, h, rec_succ f g h0 h, bit_toNat, testBit_translate' (rec_size f g h0 h)]

/-! ### Multiplication -/

def bitwise_mul.sh (x y i j : Nat) : Bool :=
  if j ≤ i then
    x.testBit (i - j) ∧ y.testBit j
  else
    false

mutual
def bitwise_mul.res (x y : Nat) : Nat → Nat → Bool
  | i, 0     => sh x y i 0
  | 0, _     => sh x y 0 0
  | i, j + 1 =>
    ((res x y i j) ^^ (sh x y i (j + 1))) ^^ carry x y i (j + 1)

def bitwise_mul.carry (x y : Nat) : Nat → Nat → Bool
  | _, 0          => false
  | 0, _          => false 
  | i + 1, j + 1  =>
    if j < i then
      (res x y i j && sh x y i (j + 1)) || ((res x y i j ^^ sh x y i (j + 1))) && carry x y i (j + 1)
    else
      false
end
termination_by
  bitwise_mul.res x y i j   => i + j + 1
  bitwise_mul.carry _ _ i j => i + j

open bitwise_mul

lemma bitwise_mul_res_zero : bitwise_mul.res x y 0 n = bitwise_mul.sh x y 0 0:= by
  cases' n <;> simp [bitwise_mul.res, bitwise_mul.sh]
  
lemma bitwise_mul_carry_zero : bitwise_mul.carry x y 0 n = false:= by
  cases' n <;> simp [bitwise_mul.carry]

def bitwise_mul' (x y n: Nat) := toNat (λ j => bitwise_mul.res x y j (n - 1)) 0 (n - 1)

def bitwise_mul (x y n : Nat) : Nat := go x y 0 (n - 1)
where
  go (x y z : Nat) : Nat → Nat
  | 0     => z.bit (bitwise_mul.res x y 0 (n - 1))
  | i + 1 => go x y (z.bit (bitwise_mul.res x y (i + 1) (n - 1))) i

theorem res_scale_two_pow_new (h: i < w ∨ j< w) : bitwise_mul.res x (2^w+y) i j = bitwise_mul.res x y i j ∧ bitwise_mul.carry x (2^w+y) i j = bitwise_mul.carry x y i j := by
  have ⟨k, hk⟩ : (∃ k : Nat, k = i+j) := by use (i+j)
  induction' k using Nat.strongInductionOn with k ih generalizing i j
  cases' k with k
  · replace hk := eq_zero_of_add_eq_zero (Eq.symm hk) 
    simp [hk, bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh]
    rw [← testBit_translate_one (by cases' h <;> linarith)]
  · cases' i with i <;> cases' j with j 
    rotate_left 3
    · have H2: k = succ i + j  ∧ k = i + succ j := ⟨by linarith, by linarith⟩
      by_cases hij: j + 1< succ i
      · have H: j < w ∧ succ j < w := by apply And.intro <;> cases' h <;> linarith
        have H3: j < i ∧ j+1 ≤ i ∧ j+1 ≤ succ i := ⟨by linarith, by linarith, by linarith⟩
        simp [bitwise_mul.res, bitwise_mul.carry, hij, H3, bitwise_mul.sh, ih k _ (Or.inr H.2) H2.2, ih k _ (Or.inr H.1) H2.1]
        simp [ih (k-1) (by simp_arith) (by right; linarith) (show k-1 = i+j by aesop)]
        simp [← testBit_translate_one, H.2]
      · have H3 : ¬ j < i  ∧ ¬ j+1 ≤ i := ⟨by linarith, by linarith⟩
        have hi3: ¬ j+1 ≤ succ i ∨ succ i = j+1 := by push_neg at *; exact lt_or_eq_of_le hij
        have H: succ i < w ∧ i< w := by apply And.intro <;> cases' h <;> linarith
        cases'  hi3 with hi3 hi3
        <;> simp [bitwise_mul.res, bitwise_mul.carry,  hi3, H3, bitwise_mul.sh]
        · simp [ih k _ (Or.inl H.2) H2.2, ih k _ (Or.inl H.1) H2.1]
        · simp [← testBit_translate_one (hi3 ▸ H.1), ih k _ (Or.inl (hi3 ▸ H.1)) (hi3 ▸ H2.1)]
    all_goals {simp [hk, bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh, ← testBit_translate_one (show 0 < w by cases' h <;> linarith)]}

theorem scale_two_pow_bit_new (h: y< 2^w): ((bitwise_mul.res x (2^w+y) w w) = ((bitwise_mul.res x y w w) ^^ (x.testBit 0))) ∧  (bitwise_mul.carry x (2^w+y) w w= bitwise_mul.carry x y w w) := by
  cases' w with w
  · cases' h3 : y.testBit 0
    <;> simp [bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh, testBit_add, bitwise_carry, h3]
  · simp [bitwise_mul.res, bitwise_mul.carry, bitwise_mul.sh, res_scale_two_pow_new (Or.inr (lt_succ_self w)), testBit_translate_one' h, lt_two_pow_testBit_false h (show w+1 ≤ w+1 by simp)]

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
    · simp [bitwise_mul.carry, ih, bitwise_mul.sh, lt_two_pow_testBit_false h0 (show w+1 ≤ succ n by linarith)]

theorem res_n_eq_res_w' (h: w ≤ n) (h1: w ≤ i) (h0: y< 2^(w+1)): bitwise_mul.res x y i n = bitwise_mul.res x y i w := by
  cases' lt_or_eq_of_le h with h2 h2; clear h
  · have ⟨k, hk1, hk2⟩ :∃ k, n = w+k ∧ 0 < k := by use n-w; rw[add_comm]; simp [Nat.sub_add_cancel (le_of_lt h2), h2]
    have := lt_two_pow_testBit_false h0 (show w+1 ≤ succ (w+k) by linarith)
    cases' i with i
    · simp [hk1, bitwise_mul.res, bitwise_mul_res_zero, this]
    · induction' k with k ih generalizing n
      · simp at hk2
      · simp [hk1, add_succ, bitwise_mul.res, bitwise_mul.sh, bitwise_mul.carry]
        have H:= lt_two_pow_testBit_false h0 (show w+1 ≤ succ (w+k) by linarith)  
        simp [H, res_n_eq_res_w, carry_n_eq_false (show w < succ (w+k) by linarith) h0]
        cases' k with k
        · simp
        · simp [ih (show w < w+succ k by linarith) rfl (succ_pos k) H]
  · simp [h2]


theorem res_n_eq_res_w'' (x: Nat) (h: i < n) (h1: k ≤ m) (h0: y < 2^(i+1)): bitwise_mul.res x y k m = bitwise_mul.res x y k n := by
  cases' le_or_gt i k with h2 h2
  · rw [res_n_eq_res_w' (show i ≤ m by linarith) h2 h0, res_n_eq_res_w' (show i ≤ n by linarith) h2 h0]
  · rw [res_n_eq_res_w h1, res_n_eq_res_w (show k ≤ n by linarith)]

theorem mul_two_pow (h: j < i): testBit (x*2^i) j = false := by
  simp only [testBit, shiftr_eq_div_pow]
  have: x * 2 ^ i / 2 ^ j = 2 ^ (i-j)*x := by
    rw [Nat.div_eq_iff_eq_mul_right (two_pow_pos j) (dvd_mul_of_dvd_right (pow_dvd_pow 2 (le_of_lt h)) x), ← mul_assoc, ← pow_add]
    rw [add_sub_of_le (le_of_lt h), mul_comm]
  have H: x * 2 ^ i / 2 ^ j % 2 = 0 := by
    rw [this, mod_eq_zero_of_dvd ((show 2^(succ 0) = 2 by simp) ▸ dvd_mul_of_dvd_left (pow_dvd_pow 2 (succ_le_iff.mpr (tsub_pos_of_lt h))) x)]
  cases' h1: bodd (x*2^i / 2^j) <;> simp [H, mod_two_of_bodd, h1] at *

theorem mul_two_pow_gen (h: i ≤ n) : testBit (x*2^i) n = testBit x (n-i) := by
  simp only [testBit, shiftr_eq_div_pow]
  nth_rewrite 1 [← Nat.sub_add_cancel h, pow_add, Nat.mul_div_mul_right _ _ (two_pow_pos i)]; rfl


theorem helper_of_main (h0: 0<i) (H2: j < 2*n) (h2: i ≤ n) (hij: j < i): bitwise_carry (x * 2 ^ i) (x * (y % 2 ^ i)) j = false := by 
  induction' j with j hj
  · simp [bitwise_carry]
  · simp [bitwise_carry, hj (by linarith) (by linarith), mul_two_pow (show j < i by linarith)]
  

theorem helper_of_main1 (h0: 0<i) (H2: j < 2*n) (h2: i ≤ n) (h: ∀ k < 2*n, bitwise_mul.res x ( y % 2 ^ i) k n = testBit ( x * (y % 2 ^ i)) k ) (h1: i ≤ j): bitwise_carry (x * 2 ^ i) (x * (y % 2 ^ i)) j = bitwise_mul.carry x (2 ^ i + y % 2 ^ i) j i := by
  have H: (y % (2^i)) < 2^i :=by simp [two_pow_pos, mod_lt]
  have ⟨i', hi'⟩ : ∃i', i =succ i' := by use pred i; simp [Nat.succ_pred_eq_of_pos h0]
  rw [hi'] at h1 H h h2 h0 ⊢
  induction' j with j hj
  · simp [bitwise_carry, bitwise_mul.carry]
  · cases' (lt_or_eq_of_le h1) with h1 h1
    · simp [bitwise_carry, bitwise_mul.carry, (succ_lt_succ_iff).mp h1]
      rw [Bool.and_comm]
      simp [bitwise_mul.sh, (show i'+1 ≤ j by linarith)]
      rw [(@res_scale_two_pow_new j (succ i') i' x (y % 2 ^ (succ i')) (Or.inr (by linarith))).1]
      have H3:= h j (show j < 2*n by linarith)
      rw [res_n_eq_res_w' (show i'≤ n by linarith) (show i' ≤ j by linarith) H] at H3
      rw [H3, hj (by linarith) (by linarith)]
      rw [mul_two_pow_gen (show succ i' ≤ j by linarith)]
      simp [testBit_translate_one' H, Bool.xor_comm]
    · simp [bitwise_carry, bitwise_mul.carry, h1, mul_two_pow (lt_succ_self j)]
      simp [helper_of_main (h1 ▸ h0) (show j < 2*n by linarith) (h1 ▸ h2) (lt_succ_self j)]

theorem helper_main (h0: 0<i) (H2: j < 2*n) (h2: i ≤ n) (h: ∀ k < 2*n, bitwise_mul.res x ( y % 2 ^ i) k n = testBit ( x * (y % 2 ^ i)) k ): bitwise_mul.res x (2 ^ i + y % 2 ^ i) j n = testBit (x * 2 ^ i + x * (y % 2 ^ i)) j:= by
  have H: (y % (2^i)) < 2^i :=by simp [two_pow_pos, mod_lt]
  have ⟨i', hi'⟩ : ∃i', i =succ i' := by use pred i; simp [Nat.succ_pred_eq_of_pos h0]
  rw [hi'] at H h h2 h0 ⊢
  rw [testBit_add]
  cases' j with j
  · simp [bitwise_mul_res_zero, bitwise_mul.sh, bitwise_carry, ← testBit_translate_one, *] at * 
    simp [bitwise_mul_res_zero, bitwise_mul.sh, ← h 0 (by linarith), mul_two_pow]
  · cases' lt_trichotomy (succ j) (succ i') with h1 h1 
    · rw [(res_scale_two_pow_new (Or.inl h1)).1, h (succ j) H2, mul_two_pow h1]
      simp [mul_two_pow _, helper_of_main h0 H2 h2 h1]
    · cases' h1 with h1 h1
      · rw [h1, ← h (succ i') (h1 ▸ H2), res_n_eq_res_w (by linarith)]
        rw [res_n_eq_res_w (show succ i' ≤  n by linarith), (scale_two_pow_bit_new H).1]
        simp[bitwise_carry, scale_two_pow_bit_new H, mul_two_pow]
        simp [(succ_inj').mp h1 ▸ helper_of_main h0 (lt_trans (lt_succ_self j) H2) h2 (by linarith)]
        simp [mul_two_pow_gen, Bool.xor_comm] 
      · rw [res_n_eq_res_w' h2 (by linarith) (by simp[two_pow_succ (succ i'), H])]
        simp [bitwise_mul.res, bitwise_mul.sh, le_of_lt h1, lt_of_succ_lt_succ h1, (show i' +1 ≤ j by linarith), helper_of_main1 h0 H2 h2 h (by linarith)]
        rw [testBit_translate_one' H]
        rw [mul_two_pow_gen (le_of_lt h1)]
        rw [(@res_scale_two_pow_new (succ j) (succ i') i' x (y % 2 ^ (succ i')) (Or.inr (by linarith))).1]
        have H3:= h (succ j) H2
        rw [res_n_eq_res_w' (show i' ≤ n by linarith) (show i' ≤ succ j by linarith) H] at H3
        rw [H3]
        simp [mul_two_pow_gen (le_of_lt h1)]
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
 
theorem bitwise_mul_size (h: 0 < n) : bitwise_mul x y n < 2^n := by
  rw [← Nat.sub_add_cancel h]
  simp [bitwise_mul, rec_size (bitwise_mul.go (n-1+1) x y) (λ v => bitwise_mul.res x y v (n-1)) (by simp[bitwise_mul.go]) (by simp[bitwise_mul.go])]

theorem bitwise_mul_testBit (h1: i< n) : (bitwise_mul x y n).testBit i = bitwise_mul.res x y i (n-1) := by
  simp [bitwise_mul]
  exact rec_testBit (λ v => bitwise_mul.res x y v (n-1)) (by simp[bitwise_mul.go]) (by simp[bitwise_mul.go]) (le_pred_of_lt h1)

theorem bitwise_mul_eq_mul' (y: Nat)  (h: i ≤ n) (h1: x < 2^n): bitwise_mul x (y%(2^i)) (2*n) = x * (y%(2^i)):= by
  cases' eq_zero_or_pos n with Hn Hn
  · simp [Hn] at h; simp [h, Hn, bitwise_mul, bitwise_mul.go, mod_one, res_zero]
  apply eq_of_testBit_eq_lt (bitwise_mul_size (succ_mul_pos 1 Hn)) (by linarith [pow_add 2 i n, Nat.mul_lt_mul' (le_of_lt (mod_lt y (two_pow_pos i))) h1 (two_pow_pos i), (pow_le_pow (show 1 ≤ 2 by linarith) (show i+n ≤ succ 1 * n by linarith[h]))])
  have H: ∀i, (y % (2^i)) + 2^i < 2^(i+1) :=by simp [two_pow_pos, mod_lt, add_lt_add, two_pow_succ]
  intros j hj
  simp only [bitwise_mul]
  rw [rec_testBit (λ v => bitwise_mul.res x (y % 2 ^ i) v (2*n - 1)) (by simp[bitwise_mul.go]) (by simp[bitwise_mul.go]) (le_pred_of_lt hj)]
  induction' i with i ih generalizing j
  · simp[mod_one, res_zero]
  · rw [mod_two_pow_succ y i]
    cases' h1:y.testBit i
    · simp [Bool.toNat, ih (by linarith) j hj]
    · simp only [Bool.toNat, cond, mul_one]
      rw [mul_add]
      cases' eq_zero_or_pos i with hi hi
      · simp [mod_one, hi, res_one] 
      · rw [← helper_main hi hj (by linarith) (by intros k hk; rw [← res_n_eq_res_w'' x (show i < n by linarith) (le_pred_of_lt hk) (lt_of_add_lt_of_nonneg_left (H i) (zero_le (2^i))), ih (by linarith) k hk])]
        rw [res_n_eq_res_w'' x (show i < n by linarith) (le_pred_of_lt hj) (Nat.add_comm _ _ ▸ (H i))]

theorem testBit_eq_mod_two_pow (h: j < n): x.testBit j = (x%(2^n)).testBit j := by
  simp only [testBit, shiftr_eq_div_pow]
  induction' n with n ih generalizing j
  · simp at h
  · have := (dvd_iff_mod_eq_zero (2 ^ j) (2^n * Bool.toNat (testBit x n))).1 (dvd_mul_of_dvd_left (pow_dvd_pow 2 (le_of_lt_succ h)) (Bool.toNat (testBit x n)))
    have h1:= two_pow_pos j
    rw [mod_two_pow_succ, add_div h1, this, zero_add]
    simp [show ¬ 2^j ≤ x%2^n %2^j by simp[mod_lt (x%(2^n)) h1]]
    cases' lt_or_eq_of_le (le_of_lt_succ h) with h1 h1
    · have h2:= @mul_two_pow j n (Bool.toNat (testBit x n)) h1
      simp_rw [testBit, shiftr_eq_div_pow, Nat.mul_comm, h2, ih h1] at *
      aesop
    · rw [h1]
      cases' h2: bodd (x/2^n)
      <;> simp [Nat.div_eq_zero, testBit, h2, shiftr_eq_div_pow]

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
  rw [← bitwise_mul_eq_mul' y rfl.ge (by simp [mod_lt, two_pow_pos])]
  apply eq_of_testBit_eq_lt (bitwise_mul_size h) (by simp [mod_lt, two_pow_pos])
  intros j hj
  rw [← testBit_eq_mod_two_pow hj, bitwise_mul_testBit hj, bitwise_mul_testBit (show j < 2*n by linarith)]
  rw [res_n_eq_res_w (le_pred_of_lt hj), res_n_eq_res_w (show j ≤ 2*n-1 by rw [show 2*n-1 = n + (n-1) by simp[(show 2 = 1+1 by simp), add_mul, Nat.add_sub_assoc h]]; exact le_of_lt (Nat.lt_add_right j n (n-1) hj))]
  rw [(res_eq_of_testBit_eq h (fun k hk => (testBit_eq_mod_two_pow hk).symm) (fun k hk => (testBit_eq_mod_two_pow hk).symm) hj hj).1]

theorem testBit_mul : (x*y).testBit i = bitwise_mul.res x y i i := by 
  have ⟨n, hn1, hn2, hi⟩: ∃ n, x < 2^n ∧ y < 2^n ∧ i< n := by
    set m:= max (max x y) (i+1); use m
    simp [lt_two_pow, lt_of_lt_of_le (lt_two_pow _) (pow_le_pow (by simp) (show x ≤ m by simp)), lt_of_lt_of_le (lt_two_pow _) (pow_le_pow (by simp) (show y ≤ m by simp))]
  rw [← mod_eq_of_lt hn2]
  rw [← bitwise_mul_eq_mul' y rfl.ge hn1, bitwise_mul_testBit (by linarith)]
  rw [res_n_eq_res_w (show i ≤ 2*n-1 by rw [show 2*n-1 = n + (n-1) by simp[(show 2 = 1+1 by simp), add_mul, Nat.add_sub_assoc (pos_of_gt hi)]]; exact le_of_lt (Nat.lt_add_right i n (n-1) hi))]


/-! ### Extraction -/

@[simp] def bitwise_extract (x i j: Nat) : Nat := toNat (λ k => (x.testBit (k+j))) 0 (i - j + 1)
  
theorem shiftRight_eq_shiftr: n >>> m = Nat.shiftr n m := by
  simp only [HShiftRight.hShiftRight, ShiftRight.shiftRight]
  induction' m with m hm generalizing n
  <;> simp [Nat.shiftr, Nat.shiftRight, Nat.div2_val, *]

theorem bitwise_extract_eq_extract : bitwise_extract x i j = (x >>> j)%(2^(i - j + 1)):= by
  apply eq_of_testBit_eq_lt (toNat_lt) (by simp [mod_lt, two_pow_pos])
  intros k hk
  rw [toNat_testBit hk, ← testBit_eq_mod_two_pow hk]
  simp [shiftRight_eq_shiftr, testBit, shiftr_eq_div_pow, Nat.div_div_eq_div_mul, pow_add, mul_comm]


/-! ### Concatenation -/

@[simp] def bitwise_concat (x y n m: Nat) : Nat := toNat (λ k => if k < n then x.testBit k else y.testBit (k - n)) 0 (n + m)

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

theorem bitwise_lt (hx : x < 2^n) (hy: y< 2^n) (h: f false false = false): bitwise f x y < 2^n := by
  rw [bitwise_eq_bitwise' f h]
  apply lt_of_testBit n (by simp[testBit_bitwise' h x y n, lt_two_pow_testBit_false hx rfl.le, lt_two_pow_testBit_false hy rfl.le, h]) (testBit_two_pow_self n)
  intro j hj
  rw[testBit_bitwise' h x y j, lt_two_pow_testBit_false hx (le_of_lt hj), lt_two_pow_testBit_false hy (le_of_lt hj), h, testBit_two_pow_of_ne (ne_of_lt hj)]

lemma append_lt (hx : x < 2^n) (hy: y< 2^m) : y <<< n ||| x < 2^(n+m) := by
  have H: x < 2^(n+m) ∧ y*2^n < 2^(n+m):= by
    apply And.intro
    · exact lt_of_lt_of_le hx ((pow_add 2 n m).symm ▸ le_mul_of_one_le_right' (by linarith))
    · rw [pow_add, mul_comm]; simp[hy, mul_lt_mul_left (two_pow_pos n)]
  simp only [lor, shiftLeft_eq]; exact bitwise_lt H.2 H.1 rfl


theorem bitwise_concat_eq_concat (hx : x < 2^n) (hy: y< 2^m): bitwise_concat x y n m = y <<< n ||| x := by
  apply eq_of_testBit_eq_lt (toNat_lt) (append_lt hx hy)
  intros k hk
  rw [toNat_testBit hk]
  by_cases h1: k <n
  <;> simp only [h1, ge_iff_le, ite_true, ite_false, shiftLeft_eq, HOr.hOr, OrOp.or, lor, or_eq_or', lor']
  <;> rw [testBit_bitwise' (by simp)]
  · simp [mul_two_pow h1]
  · rw [mul_two_pow_gen (by linarith), lt_two_pow_testBit_false hx (by linarith)]; simp

lemma or_eq_xor (h: b = true → b' =false): (b || b') =  (b ^^ b') := by 
  cases' h1 : b <;> cases' h2: b' <;> simp [h1, h2, h] at * 

lemma append_eq_add_testBit  (hx : x < 2^n) (hy: y< 2^m) (hk : k < n+m): (y <<< n ||| x).testBit k = (y*2^n + x).testBit k := by
  simp only [HOr.hOr, OrOp.or, lor]
  rw [testBit_add, or_eq_or', lor', testBit_bitwise' (by decide)]
  have H : ∀ j : Nat, (y*2^n).testBit j = true → x.testBit j = false := by
      intros j h1; by_cases h2: j < n <;> push_neg at h2
      <;> simp [lt_two_pow_testBit_false hx, mul_two_pow, h2] at *
  apply @And.left _ (bitwise_carry (y*2^n) x k = false) _
  induction' k with k ih <;> simp only [bitwise_carry]
  · simp [or_eq_xor (H 0)]
  · cases' h2: x.testBit k <;> cases' h3: (y*2^n).testBit k 
    <;> simp [h3, (ih (lt_trans (lt_succ_self k) hk)).2, or_eq_xor (H (succ k)), H k _] at h2 ⊢

theorem append_eq_add (hx : x < 2^n): y <<< n ||| x = y*2^n + x := by
  apply eq_of_testBit_eq_lt (append_lt hx (lt_two_pow y)) _ (fun j hj => append_eq_add_testBit hx (lt_two_pow y) hj)
  calc y*2^n + x ≤ (2^y-1)*2^n + x      := by simp [Nat.le_pred_of_lt (lt_two_pow y)]
       _         < (2^y-1)*2^n + 2^n    := by linarith
       _         = 2^n*2^y - 2^n + 2^n  := by simp [mul_comm, mul_tsub (2^n) (2^y) 1]
       _         = 2^(n+y)              := by rw [Nat.sub_add_cancel            (le_mul_of_one_le_right' (Nat.one_le_pow' y 1)), ← pow_add]
  

/-! ### Equality -/

def bitwise_eq (x y n: Nat) : Prop := go x y (n-1)
where
  go (x y : Nat) : Nat → Prop
  | 0     => x.testBit 0 == y.testBit 0
  | i + 1 => (x.testBit (i+1) == y.testBit (i+1)) ∧ go x y i

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

theorem bitwise_eq_eq (h: 0 < n) (hx : x < 2^n) (hy: y < 2^n ): (x = y) = bitwise_eq x y n := by
  rw [bitwise_eq_eq_forall h]
  apply propext; apply Iff.intro
  <;> intro H
  · simp[H]
  · apply eq_of_testBit_eq_lt hx hy
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

/-! ### Signed extension -/

@[simp] def bitwise_ext (x n k: Nat) := toNat (λ i => if i < n then x.testBit i else x.testBit (n - 1)) 0 (n + k)

lemma bitwise_ext_zero (hx: x < 2^w) : bitwise_ext x w 0 = x := by
  apply eq_of_testBit_eq_lt (toNat_lt) hx
  intro j hj 
  simp [toNat_testBit hj, hj]


/-! ### Division -/

def uDivModRec (a b w : Nat) : (Nat × Nat) := go a b w w
where
  go (a b l w: Nat) :=
  match w with
  | 0    => (0, 0)
  | w + 1 =>
    if a == 0 then (0, 0)
    else
      let (q1, r1) := go (a >>> 1) b l w --want to use bitwise shift right instead of a >>> 1 same thing below
      let (q1, r1) := (q1 <<< 1, r1 <<< 1)
      let r1ShiftAdd := bitwise_add r1 (a%2) l
      let notB := bitwise_neg b l
      let rMinusB := bitwise_add r1ShiftAdd notB l
      let sign := !(bitwise_carry r1ShiftAdd notB l)
      let q1 := if sign then q1 else (q1 + 1)
      let r1 := if sign then r1ShiftAdd else rMinusB
      (q1, r1)

def UdivUremBB (a b w : Nat) : (Nat × Nat) :=
  if b == 0 then (toNat (λ _ => true) 0 w, a)
  else uDivModRec a b w

--Carry is 0 indexed. BVs are 0 indexed. But bitwise_operations are not :(.
-- ^ this is now fixed :))
--It seems like we need to set `w` to the max length of `a` and `b`.
-- i.e. a < 2^w b < 2^w

#eval uDivModRec 1 1 4
#eval uDivModRec.go 10 200 7 4
#eval uDivModRec 0 15 0
#eval bitwise_neg 15 3
#eval bitwise_add 1 1 3
#eval uDivModRec 277 45 9
#eval uDivModRec 1 0 1
#eval uDivModRec.go 10 0 12 12
#eval testBit 10 4
#eval !(bitwise_carry 10 (bitwise_neg 0 (4-1)) 4)
#check bitwise_neg_eq_neg
#check bitwise_add_eq_add
#eval bitwise_carry (1 % 2 ^ (5 + 1)) (bitwise_neg 0 5) (5 + 1)
#eval 1/0 --should be the BV of all 1s

lemma zero_or_one_or_gt_one (n: ℕ) : n = 0 ∨ n = 1 ∨ 1 < n := by
  cases' le_or_gt n 1 with h h
  · interval_cases n <;> simp
  · simp [h]

lemma one_mod_lt (h: 1 < n) : 1 % n = 1 := Nat.sub_add_cancel (show 2 ≤ n by linarith) ▸ one_mod (n-2)

lemma lt_carry_false (h : 0 < b) (ha : a < 2^w) (hb : b < 2^w): a < b ↔ !(bitwise_carry a (bitwise_neg b w) w) := by
  rw [bitwise_neg_eq_neg hb]
  rw [mod_eq_of_lt (sub_lt (two_pow_pos (w)) h)]
  have h1:= @testBit_add a (2^w -b) w
  rw [lt_two_pow_testBit_false ha (le_refl w)] at h1
  rw [lt_two_pow_testBit_false (sub_lt (two_pow_pos w) h) (le_refl w)] at h1
  simp only [Bool.xor_false_left] at h1
  rw [← h1]
  apply Iff.intro
  · intro h2
    rw [lt_two_pow_testBit_false (by zify[le_of_lt hb] at *; linarith) (le_refl w)]; simp
  · contrapose!; intro h2
    rw [← Nat.add_sub_assoc (le_of_lt hb), add_comm, Nat.add_sub_assoc h2]
    rw [testBit, shiftr_eq_div_pow, Nat.add_div_of_dvd_right (dvd_refl _)]
    simp [Nat.div_eq_zero (lt_of_le_of_lt (sub_le _ _) ha)]

lemma shiftRight_eq_div_two : a >>> 1 = a / 2 := shiftRight_eq_shiftr ▸ shiftr_eq_div_pow a 1 
lemma shiftLeft_eq_two_mul : a <<< 1 = 2*a := Nat.mul_comm _ _ ▸ shiftLeft_eq a 1

lemma uDivModRec_zero : uDivModRec.go 0 b w v = (0, 0) := by
  cases' v <;> simp [uDivModRec.go]

lemma uDivModRec_one (h0 : 0 < b) (h : b < 2^w) : uDivModRec.go 1 b w (v + 1) = (1 / b, 1 % b) := by
  cases' w with w
  · simp only [lt_one_iff, zero_eq, pow_zero] at h; simp [h] at h0
  · simp only [uDivModRec.go, ite_false, bitwise_add_eq_add, shiftLeft_eq_two_mul, shiftRight_eq_div_two]
    simp only [@Nat.div_eq_zero 1 2 (by decide), uDivModRec_zero, succ_sub_succ_eq_sub, tsub_zero]
    simp only [← lt_carry_false h0 (mod_lt _ (two_pow_pos _)) h, mul_zero, one_mod, zero_add]
    rw [one_mod_lt (le_self_pow (ne_zero_of_lt (succ_pos w)) 2)]
    cases' eq_or_gt_of_le (one_le_of_lt h0) with hb hb
    · rw [bitwise_neg_eq_neg h]
      simp [hb, Nat.add_sub_of_le (one_le_two_pow _)]
    · simp [hb, Nat.div_eq_zero hb, one_mod_lt hb]

lemma div_mod_two_mul : a/b = 2*(a/2/b) + a/b%2 := by
  nth_rewrite 1 [← div_add_mod (a/b) 2]
  congr 1
  rw [Nat.div_div_eq_div_mul, mul_comm b 2, Nat.div_div_eq_div_mul]

lemma mod_two_mul : a%b + b*(a/b % 2)= a%(2*b)  := by
  rw [← mod_mul_left_div_self, add_comm, ← mod_mul_left_mod a 2 b]
  simp only [div_add_mod]

lemma helper : a%(2*b) = 2*(a/2%b) + a%2 := by
  rw [← mod_mul_right_div_self, ← mod_mul_right_mod a 2 b, div_add_mod]

lemma helper2 (h0: 0 < b) : a%(2*b) < b ↔ a/b%2 = 0 := (mod_mul_left_div_self _ _ _).symm ▸ (Nat.div_eq_zero_iff h0).symm


--this is the most annoying lemma. why is the proof so long?
lemma lt_div_succ_pow (h : a < 2^(v+1)) : a/2 < 2^ v := by
  have : 2^(v+1)/2 = 2^v := by
    rw [← Nat.add_sub_cancel v 1, ← pow_div (by linarith) (by decide)]; simp
  simpa [← this] using div_lt_div_of_lt_of_dvd ((pow_succ _ _).symm ▸ dvd_mul_left 2 (2^v)) h

-- this induction is not clean :(
#check succ_pred_eq_of_pos
lemma uDivModRec_ih (hb : b < 2^w ) (ha : a < 2^v) (h0 : 0 < b) (hv : v ≤ w): uDivModRec.go a b w v = (a / b, a % b) := by
  cases' v with v
  · simp only [zero_eq, pow_zero, lt_one_iff] at ha; simp [uDivModRec_zero, ha]
  · induction' a using Nat.strongInductionOn with a ih generalizing v
    have H:= lt_of_lt_of_le ha (pow_le_pow_of_le_right (show 2 > 0 by decide) hv)
    rcases zero_or_one_or_gt_one a with ha1 | ha2 | ha2
    · simp [uDivModRec.go, ha1]
    · rw [ha2, uDivModRec_one h0 hb]
    · simp only [uDivModRec.go, beq_iff_eq, (show a ≠ 0 by linarith), ite_false, Nat.add]
      rw [div_mod_two_mul]
      have hv1 : 1 < succ v := (pow_lt_pow_iff (show 1 < 2 by decide)).mp (lt_of_le_of_lt (show 2^1 ≤ a by linarith) ha)
      specialize @ih (a/2) (Nat.div_lt_self (by linarith) (by decide)) (v-1)
      rw [← pred_eq_sub_one, succ_pred_eq_of_pos (by linarith [hv1])] at ih 
      simp only [shiftRight_eq_div_two, shiftLeft_eq_two_mul, bitwise_add_eq_add, ih (lt_div_succ_pow ha) (le_trans (by linarith) hv)]
      simp only [← lt_carry_false h0 (mod_lt _ (two_pow_pos _)) hb, ← helper]
      simp only [mod_eq_of_lt (lt_of_le_of_lt (mod_le a (2*b)) H), helper2 h0]
      rw [bitwise_neg_eq_neg hb]
      have := @mod_two_mul a b
      cases' mod_two_eq_zero_or_one (a/b) with hC hC 
      <;> simp only [hC, one_ne_zero, ite_false, add_mod_mod, Prod.mk.injEq, ite_true, mul_zero, add_zero, true_and, mul_one] at this ⊢
      · rw [this]
      · rw [← Nat.add_sub_assoc (le_of_lt hb)]
        rw [Nat.sub_add_comm (not_lt.mp (mt ((helper2 h0).mp) (ne_zero_of_eq_one hC)))]
        simp only [add_mod_right]
        rw [mod_eq_of_lt (lt_of_le_of_lt (le_trans (Nat.sub_le _ b) (mod_le _ _)) H)]
        simp [← this]

theorem uDivModRec_eq_div (h0 : 0 < b) (hb : b < 2^w) (ha: a < 2^w) : uDivModRec a b w = (a / b, a % b) := by
  cases' w with w <;> simp only [uDivModRec]
  · rw [pow_zero, lt_one_iff] at hb ha; simp [hb, ha]
  · rw [uDivModRec_ih hb ha h0 rfl.le]

theorem UdivUremBB_eq_div (hb : b < 2^w) (ha: a < 2^w) : UdivUremBB a b w = if b = 0 then (2^w - 1, a) else (a / b, a % b) := by
  cases' b with b
  · simp only [UdivUremBB, ite_true]; congr
    apply eq_of_testBit_eq_lt (toNat_lt) (by simp [sub_lt])
    intros j hj
    rw [testBit_two_pow_minus_one (by linarith) hj, toNat_testBit hj]
  . exact uDivModRec_eq_div (by linarith) hb ha


end Nat



