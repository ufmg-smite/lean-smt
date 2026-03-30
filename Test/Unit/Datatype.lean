import Smt

inductive Color where
  | red
  | green
  | blue

example : Color.red ≠ Color.blue := by
  intro hrb
  nomatch hrb

example : Color.red ≠ Color.blue := by
  smt

inductive mynat where
 | zero
 | succ (n : mynat)

def mynat.add : mynat → mynat → mynat
 | m, .zero => m
 | m, .succ n => .succ (add m n)

def mynat.mul : mynat → mynat → mynat
 | _, .zero => .zero
 | m, .succ n => add (mul m n) m

example : .zero ≠ mynat.succ .zero := by
  smt

inductive mynat' where
 | zero
 | succ :  mynat' → mynat' → mynat'

example : .zero ≠ mynat'.succ .zero .zero := by
  smt



-- Add more examples.
example {p q r : U → Prop} : (∀ x, p x ∧ q x ∧ r x) = ((∀ x, p x) ∧ (∀ x, q x) ∧ (∀ x, r x)) := by
  smt

set_option trace.smt true
example (add : mynat → mynat → mynat) (sum : mynat → mynat) (div2 : mynat → mynat) (mul : mynat → mynat → mynat)
  (hadd : ∀ m, add m .zero = m) (hadd' : ∀ m n, add m (.succ n) = .succ (add m n))
  (hmul : ∀ m, mul m .zero = .zero) (hmul' : ∀ m n, mul m (.succ n) = add (mul m n) m)
  (hmuladd : ∀ m n k, mul m (add n k) = add (mul m n) (mul m k))
  -- (haddcomm : ∀ m n, add m n = add n m)
  (hmulcomm : ∀ m n, mul m n = mul n m)
  -- (hdiv2 : div2 .zero = .zero) (hdiv2' : div2 (.succ .zero) = .zero) (hdiv2'' : ∀ n, div2 (.succ (.succ n)) = .succ (div2 n))
  (h : sum .zero = .zero) (h1 : ∀ n, sum (mynat.succ n) = add (sum n) (.succ n)) :
  ∀ n, mul (.succ (.succ .zero)) (sum n) =  mul (.succ n) n := by
  intros n
  induction n with
  | zero => smt [*]
  | succ n ih => smt [*]

theorem mynat.add_assoc :
  ∀ m n k, mynat.add m (mynat.add n k) = mynat.add (mynat.add m n) k := by
  intros m n k
  induction k with
  | zero => grind [mynat.add]
  | succ k ih => grind [mynat.add]

-- theorem mynat.add_comm :
--   ∀ m n, mynat.add m n = mynat.add n m := by
--   intros m n
--   induction n with
--   | zero => smt [*]
--   | succ n ih => smt [*]

-- theorem mynat.mul_add :
--   ∀ m n k, mynat.mul m (.add n k) = .add (mynat.mul m n) (mynat.mul m k) := by
--   intros m n k
--   induction k with
--   | zero => smt [*]
--   | succ k ih => sorry

-- theorem mynat.mul_comm :
--   ∀ m n, mynat.mul m n = mynat.mul n m := by
--   intros m n
--   induction n with
--   | zero => sorry
--   | succ n ih => sorry
