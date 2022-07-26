opaque Foo : Type
axiom Foo.default : Foo
axiom Foo.addNat : Foo → Nat → Foo

axiom concatNats (acc : Foo) (l : List Nat) : Foo

@[simp]
theorem concatNats_cons 
    : concatNats acc (x :: xs) =
      let acc' := acc.addNat x;
      concatNats acc' xs :=
    sorry

example : concatNats Foo.default (List.iota 10) = Foo.default := by
  -- Unfold the list
  simp only [List.iota]
  -- Try constructing let-binding sequence
  simp (config := { zeta := false }) only [concatNats_cons]

  sorry

example : concatNats Foo.default (List.iota 200) = Foo.default := by
  simp only [List.iota]
  /- tactic 'simp' failed, nested error:
  (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit) -/
  -- This simplification should not need a *single* WHNF call, no?
  -- simp (config := { zeta := false }) only [concatNats_cons]
  sorry
