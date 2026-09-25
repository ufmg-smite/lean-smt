import Mathlib
import Smt.Reconstruct.Prop.Core
import Smt.Reconstruct.Real.CAD.RootVal
import Smt.Reconstruct.Real.CAD.Utils
import Smt.Reconstruct.Real.CAD.AlgebraicNumbers.Order
import Smt.Reconstruct.Real.CAD.Sturm.SeqDefs

namespace Cover

/-- Computable comparisons on endpoint representations. -/
class Endpoint (E : Type) where
  /-- Sound test for `<` (may return `false` for incomparable representations). -/
  blt : E → E → Bool
  /-- Sound test for `=`. -/
  beq : E → E → Bool

/-- The real value of an endpoint, and soundness of the tests. Kept separate from `Endpoint` so
that the scan stays computable. -/
class Endpoint.Sound (E : Type) [Endpoint E] where
  toReal : E → Real
  blt_sound : ∀ a b : E, Endpoint.blt a b = true → toReal a < toReal b
  beq_sound : ∀ a b : E, Endpoint.beq a b = true → toReal a = toReal b

export Endpoint.Sound (toReal)

variable {E : Type} [Endpoint E]

/-- An end of a piece. -/
inductive Bound (E : Type)
  | negInf
  | fin (e : E)
  | posInf

/-- A piece of the real line: a point, or an open interval with possibly infinite ends. -/
inductive Piece (E : Type)
  | pt (r : E)
  | op (l r : Bound E)

/-- The prefix of the line covered so far: `(-∞, c)` or `(-∞, c]`. -/
inductive Reach (E : Type)
  | excl (c : Bound E)
  | incl (c : E)

/-! ### The scan -/

/-- `a < b` on bounds. -/
def Bound.ltB : Bound E → Bound E → Bool
  | .negInf, .fin _ => true
  | .negInf, .posInf => true
  | .fin a, .fin b => Endpoint.blt a b
  | .fin _, .posInf => true
  | _, _ => false

/-- The open piece `(l, _)` attaches to the covered prefix `(-∞, c)`: `l = -∞`, or `l < c`. -/
def Bound.attach : Bound E → Bound E → Bool
  | .negInf, _ => true
  | .fin l, .fin c => Endpoint.blt l c
  | .fin _, .posInf => true
  | _, _ => false

/-- The open piece `(l, _)` attaches to the covered prefix `(-∞, c]`: `l = -∞`, or `l ≤ c`. -/
def Bound.attachIncl : Bound E → E → Bool
  | .negInf, _ => true
  | .fin l, c => Endpoint.blt l c || Endpoint.beq l c
  | .posInf, _ => false

/-- One step of the scan: attach the piece to the reach if possible, otherwise skip it. -/
def step : Reach E → Piece E → Reach E
  | .excl (.fin c), .pt r => if Endpoint.beq r c then .incl c else .excl (.fin c)
  | s, .pt _ => s
  | .excl c, .op l r => if l.attach c && c.ltB r then .excl r else .excl c
  | .incl c, .op l r => if l.attachIncl c && (Bound.fin c).ltB r then .excl r else .incl c

/-- The pieces cover the whole line (sufficient condition, one pass over the list). -/
def sweep (L : List (Piece E)) : Bool :=
  match L.foldl step (.excl .negInf) with
  | .excl .posInf => true
  | _ => false

/-! ### Semantics -/

section Semantics
variable [Endpoint.Sound E]

/-- The subset of the line a piece denotes. Membership unfolds definitionally to the shape cvc5
states it: `x ∈ {r}` is `x = r`, `x ∈ Set.Ioo l r` is `l < x ∧ x < r`, and a conjunct mentioning
an infinite end is omitted (`Set.Ioi`, `Set.Iio`, `Set.univ`). Degenerate open pieces are never
emitted; they denote `∅`. -/
def Piece.set : Piece E → Set Real
  | .pt r => {toReal r}
  | .op .negInf (.fin r) => Set.Iio (toReal r)
  | .op (.fin l) .posInf => Set.Ioi (toReal l)
  | .op (.fin l) (.fin r) => Set.Ioo (toReal l) (toReal r)
  | .op .negInf .posInf => Set.univ
  | .op _ _ => ∅

/-- `x < b`. -/
def Bound.ltReal (x : Real) : Bound E → Prop
  | .negInf => False
  | .fin c => x < toReal c
  | .posInf => True

/-- `b < x`. -/
def Bound.gtReal (x : Real) : Bound E → Prop
  | .negInf => True
  | .fin l => toReal l < x
  | .posInf => False

def Reach.mem (x : Real) : Reach E → Prop
  | .excl c => c.ltReal x
  | .incl c => x ≤ toReal c

theorem Piece.mem_op {l r : Bound E} {x : Real} (hl : l.gtReal x) (hr : r.ltReal x) :
    x ∈ (Piece.op l r).set := by
  cases l <;> cases r <;> simp_all [Piece.set, Bound.gtReal, Bound.ltReal]

theorem Bound.attach_sound {l c : Bound E} {x : Real} (h : l.attach c = true) (hx : ¬ c.ltReal x) :
    l.gtReal x := by
  cases l <;> cases c <;> simp_all [Bound.attach, Bound.gtReal, Bound.ltReal]
  rename_i l c
  exact lt_of_lt_of_le (Endpoint.Sound.blt_sound l c h) hx

theorem Bound.attachIncl_sound {l : Bound E} {c : E} {x : Real} (h : l.attachIncl c = true)
    (hx : ¬ x ≤ toReal c) : l.gtReal x := by
  cases l <;> simp_all [Bound.attachIncl, Bound.gtReal]
  rename_i l
  rcases h with h | h
  · exact lt_trans (Endpoint.Sound.blt_sound l c h) hx
  · exact (Endpoint.Sound.beq_sound l c h) ▸ hx

/-- Whatever the step adds to the reach is covered by the piece. -/
theorem Piece.mem_of_step {s : Reach E} {p : Piece E} {x : Real}
    (h1 : (step s p).mem x) (h2 : ¬ s.mem x) : x ∈ p.set := by
  cases s with
  | excl c =>
    cases p with
    | pt r =>
      cases c with
      | negInf => exact absurd h1 h2
      | posInf => exact absurd h1 h2
      | fin c =>
        simp only [step] at h1
        split at h1
        · rename_i hb
          have hrc := Endpoint.Sound.beq_sound r c hb
          simp only [Reach.mem, Bound.ltReal, not_lt] at h1 h2
          simp only [Piece.set, Set.mem_singleton_iff]
          rw [hrc]
          exact le_antisymm h1 h2
        · exact absurd h1 h2
    | op l r =>
      simp only [step] at h1
      split at h1
      · rename_i hc
        have ha := (Bool.and_eq_true _ _).mp hc |>.1
        exact Piece.mem_op (Bound.attach_sound ha h2) h1
      · exact absurd h1 h2
  | incl c =>
    cases p with
    | pt r => exact absurd h1 h2
    | op l r =>
      simp only [step] at h1
      split at h1
      · rename_i hc
        have ha := (Bool.and_eq_true _ _).mp hc |>.1
        exact Piece.mem_op (Bound.attachIncl_sound ha h2) h1
      · exact absurd h1 h2

private theorem orN_cons_of {p : Prop} {qs : List Prop} (h : p ∨ orN qs) : orN (p :: qs) := by
  cases qs with
  | nil => simpa [orN] using h
  | cons q qs => simpa [orN] using h

/-- The invariant behind `cover_of_sweep`: the pieces cover everything outside the reach. -/
theorem foldl_step_covers : ∀ (L : List (Piece E)) (s : Reach E),
    L.foldl step s = .excl .posInf → ∀ x : Real, ¬ s.mem x → orN (L.map (fun p => x ∈ p.set))
  | [], s, h, x, hx => by
    simp only [List.foldl] at h
    subst h
    exact absurd trivial hx
  | p :: L, s, h, x, hx => by
    simp only [List.foldl] at h
    apply orN_cons_of
    by_cases hs : (step s p).mem x
    · exact Or.inl (Piece.mem_of_step hs hx)
    · exact Or.inr (foldl_step_covers L (step s p) h x hs)

/-- A list of pieces accepted by `sweep` covers the whole line: every real satisfies the
disjunction cvc5 concludes in `COVER`. -/
theorem cover_of_sweep (L : List (Piece E)) (h : sweep L = true) (x : Real) :
    orN (L.map (fun p => x ∈ p.set)) := by
  unfold sweep at h
  split at h
  · exact foldl_step_covers L _ (by assumption) x (by simp [Reach.mem, Bound.ltReal])
  · exact absurd h (by simp)

end Semantics

/-! ### The endpoints cvc5 uses: rationals and isolated algebraic numbers -/

open AlgebraicNumber in
/-- A rational or an algebraic number, as cvc5 represents interval endpoints. -/
inductive Num
  | rat (q : Rat)
  | alg (a : AlgNum)

open AlgebraicNumber

instance : DecidableEq Raw := fun a b =>
  decidable_of_iff (a.p = b.p ∧ a.l = b.l ∧ a.r = b.r) (by
    constructor
    · rintro ⟨h1, h2, h3⟩; cases a; cases b; simp_all
    · intro h; subst h; exact ⟨rfl, rfl, rfl⟩)

instance : DecidableEq AlgNum := Subtype.instDecidableEq

/-- Order tests on representations: rationals exactly, algebraic numbers through their isolating
intervals. Equality of algebraic numbers is equality of representations. -/
instance : Endpoint Num where
  blt
    | .rat a, .rat b => decide (a < b)
    | .rat a, .alg b => decide (a < b.l)
    | .alg a, .rat b => decide (a.r < b)
    | .alg a, .alg b => decide (a.r < b.l)
  beq
    | .rat a, .rat b => decide (a = b)
    | .alg a, .alg b => decide (a = b)
    | _, _ => false

noncomputable instance : Endpoint.Sound Num where
  toReal
    | .rat q => ratToReal q
    | .alg a => a.toReal
  blt_sound a b h := by
    cases a <;> cases b <;> simp only [Endpoint.blt, decide_eq_true_eq] at h
    · exact ratToReal_lt _ _ h
    · exact cmp_rat_alg_ra _ _ h
    · exact cmp_rat_alg_ar _ _ h
    · exact lt_toReal _ _ h
  beq_sound a b h := by
    cases a <;> cases b <;> simp only [Endpoint.beq, decide_eq_true_eq, Bool.false_eq_true] at h
    · rw [h]
    · rw [h]

open Qq in
def numOfRootVal : RootVal → Q(Num)
| .alg e _ => let a: Q(AlgNum) := e; q(.alg $a)
| .rat e _ => let q: Q(Rat) := e; q(.rat $q)

open Qq in
def reconsBound (t : cvc5.Term) : Smt.ReconstructM Q(Bound Num) :=
  match t.getKind with
  | .COV_MINUS_INFINITY => pure q(Bound.negInf)
  | .COV_PLUS_INFINITY => pure q(Bound.posInf)
  | _ => do
    let t_rv ← reconsRootVal t
    let t_num := Cover.numOfRootVal t_rv
    pure q(Bound.fin $t_num)

open Qq in
def reconsPiece (lb ub : cvc5.Term) : Smt.ReconstructM Q(Piece Num) := do
  if lb == ub then
    if lb.getKind == .COV_MINUS_INFINITY || lb.getKind == .COV_PLUS_INFINITY then
      throwError "Point interval at infinity"
    let lb_num := Cover.numOfRootVal (← reconsRootVal lb)
    pure q(Piece.pt $lb_num)
  else
    let lb_b ← reconsBound lb
    let ub_b ← reconsBound ub
    pure q(Piece.op $lb_b $ub_b)

open Qq in
/-- A piece with cvc5's endpoints as reconstructed root values. -/
def reconsPieceRV (lb ub : cvc5.Term) : Smt.ReconstructM (Piece RootVal) := do
  let bound (t : cvc5.Term) : Smt.ReconstructM (Bound RootVal) :=
    match t.getKind with
    | .COV_MINUS_INFINITY => pure .negInf
    | .COV_PLUS_INFINITY => pure .posInf
    | _ => do pure (.fin (← reconsRootVal t))
  if lb == ub then
    match ← bound lb with
    | .fin rv => pure (.pt rv)
    | _ => throwError "Point interval at infinity"
  else
    pure (.op (← bound lb) (← bound ub))

/-! ### Refining the endpoints before the scan

The tests of `Endpoint Num` compare an algebraic number through its isolating interval, and cvc5's
intervals may touch another endpoint of the cover (for `ex2`, the number isolated in `(3/4, 1)`
next to the rational `1`), in which case the test cannot decide. The scan is therefore run on
copies refined until every isolating interval is strictly separated from every rational endpoint
and from every other algebraic endpoint; all occurrences of an endpoint are refined identically,
so equality of representations is preserved. The conclusion is then restated in terms of cvc5's
representations with `refine_toReal`. -/

open Lean

/-- The pieces to scan, and for each distinct algebraic endpoint its original expression, the
refined expression, and the proof of `AlgNum.toReal refined = AlgNum.toReal original` when it was
refined. -/
structure RefinedCover where
  pieces : List Expr
  algs : Array (Expr × Expr × Option Expr)

def RefinedCover.algExpr (rc : RefinedCover) (e : Expr) : Expr :=
  match rc.algs.find? (·.1 == e) with
  | some (_, e', _) => e'
  | none => e

/-- The equations restating refined endpoints as the original ones. -/
def RefinedCover.eqs (rc : RefinedCover) : List Expr := rc.algs.toList.filterMap (·.2.2)

open Qq in
/-- The real value of an endpoint, with the refined representation. -/
def RefinedCover.toReal (rc : RefinedCover) : RootVal → Q(Real)
  | .rat e _ => let q : Q(Rat) := e; q(ratToReal $q)
  | .alg e _ => let a : Q(AlgNum) := rc.algExpr e; q(AlgNum.toReal $a)

open Qq in
def RefinedCover.num (rc : RefinedCover) : RootVal → Q(Num)
  | .rat e _ => let q : Q(Rat) := e; q(Num.rat $q)
  | .alg e _ => let a : Q(AlgNum) := rc.algExpr e; q(Num.alg $a)

open Qq in
def RefinedCover.bound (rc : RefinedCover) : Bound RootVal → Q(Bound Num)
  | .negInf => q(Bound.negInf)
  | .posInf => q(Bound.posInf)
  | .fin rv => let n := rc.num rv; q(Bound.fin $n)

open Qq in
def RefinedCover.piece (rc : RefinedCover) : Piece RootVal → Q(Piece Num)
  | .pt rv => let n := rc.num rv; q(Piece.pt $n)
  | .op l r => let lb := rc.bound l; let rb := rc.bound r; q(Piece.op $lb $rb)

/-- The endpoints of a piece. -/
def Piece.rootVals : Piece RootVal → List RootVal
  | .pt rv => [rv]
  | .op l r => (match l with | .fin rv => [rv] | _ => []) ++ (match r with | .fin rv => [rv] | _ => [])

open Lean Meta in
/-- See the section header. Fails when two representations denote the same number, since they
never separate. -/
def refineCover (L : List (Piece RootVal)) (fuel : Nat := maxRefinements) :
    Smt.ReconstructM RefinedCover := do
  let mut rats : Array Rat := #[]
  let mut algs : Array (Expr × Raw) := #[]
  for p in L do
    for rv in p.rootVals do
      match rv with
      | .rat _ q => rats := rats.push q
      | .alg e raw => if !algs.any (·.1 == e) then algs := algs.push (e, raw)
  -- refine natively until separated
  let mut cur : Array Raw := algs.map (·.2)
  let mut ks : Array Nat := algs.map fun _ => 0
  let mut round := 0
  repeat
    let indexed := cur.toList.zipIdx
    let rats' := rats
    let separated (a : Raw) (i : Nat) : Bool :=
      rats'.all (fun q => q < a.l || a.r < q)
        && indexed.all (fun (b, j) => j == i || b.r < a.l || a.r < b.l)
    let todo := (indexed.filter fun (a, i) => !separated a i).map (·.2)
    if todo.isEmpty then break
    if round ≥ fuel then
      throwError "COVER: cannot separate the algebraic endpoints {algs.map (·.1)}"
    for i in todo do
      cur := cur.modify i Raw.refine
      ks := ks.modify i (· + 1)
    round := round + 1
  -- the refined expressions and the equations back to the originals
  let mut out : Array (Expr × Expr × Option Expr) := #[]
  for ((e, _), k) in algs.zip ks do
    let mut e' := e
    let mut eq? : Option Expr := none
    for _ in [0:k] do
      -- `refine_toReal e' : e'.toReal = e'.refine.toReal`
      let step ← mkEqSymm (mkApp (mkConst ``refine_toReal) e')
      eq? := some (← match eq? with | none => pure step | some eq => mkEqTrans step eq)
      e' := mkApp (mkConst ``AlgNum.refine) e'
    out := out.push (e, e', eq?)
  let rc : RefinedCover := { pieces := [], algs := out }
  pure { rc with pieces := L.map rc.piece }

/-! ### Tests -/

namespace tests

-- (-∞, 1) ∪ {1} ∪ (1, +∞), all rational
example (x : Real) : x ∈ Set.Iio (ratToReal 1) ∨ x ∈ ({ratToReal 1} : Set Real) ∨ x ∈ Set.Ioi (ratToReal 1) :=
  cover_of_sweep (E := Num)
    (L := [.op .negInf (.fin (.rat 1)), .pt (.rat 1), .op (.fin (.rat 1)) .posInf])
    (by decide) x

-- overlapping and redundant pieces, unsorted, as cvc5 may emit them
example (x : Real) :
    x ∈ Set.Iio (ratToReal 3) ∨ x ∈ Set.Ioo (ratToReal 2) (ratToReal 5) ∨ x ∈ ({ratToReal 1} : Set Real)
      ∨ x ∈ Set.Ioi (ratToReal 4) :=
  cover_of_sweep (E := Num)
    (L := [.op .negInf (.fin (.rat 3)), .op (.fin (.rat 2)) (.fin (.rat 5)), .pt (.rat 1),
           .op (.fin (.rat 4)) .posInf])
    (by decide) x

-- membership unfolds definitionally to the shape cvc5 states
example (x : Real) : x < ratToReal 1 ∨ x = ratToReal 1 ∨ x > ratToReal 1 :=
  cover_of_sweep (E := Num)
    (L := [.op .negInf (.fin (.rat 1)), .pt (.rat 1), .op (.fin (.rat 1)) .posInf])
    (by decide) x

-- a gap is rejected
example : sweep (E := Num) [.op .negInf (.fin (.rat 1)), .op (.fin (.rat 1)) .posInf] = false := by
  decide

-- an algebraic endpoint: √2, isolated in (5/4, 3/2), mixed with rationals
def r2 : Raw := ⟨CompPoly.CPolynomial.C (-2) + CompPoly.CPolynomial.C 1 * CompPoly.CPolynomial.X ^ 2, 5/4, 3/2⟩
def a2 : AlgNum := by lift_alg_num r2

example (x : Real) :
    x ∈ Set.Iio (ratToReal 1) ∨ x ∈ ({ratToReal 1} : Set Real) ∨ x ∈ Set.Ioo (ratToReal 1) a2.toReal
      ∨ x ∈ ({a2.toReal} : Set Real) ∨ x ∈ Set.Ioi a2.toReal :=
  cover_of_sweep (E := Num)
    (L := [.op .negInf (.fin (.rat 1)), .pt (.rat 1), .op (.fin (.rat 1)) (.fin (.alg a2)),
           .pt (.alg a2), .op (.fin (.alg a2)) .posInf])
    -- the elaborator's `decide` gets stuck on `Rat` arithmetic (`@[irreducible]`); the kernel does
    -- not, and reconstruction builds the kernel-checked term directly (`mkDecideProof'`).
    (by decide +kernel) x

end tests

end Cover
