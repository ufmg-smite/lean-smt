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

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1024 in
example : concatNats Foo.default (List.iota 10) = Foo.default := by
  -- Unfold the list
  simp only [List.iota]
  -- Try constructing let-binding sequence
  simp (config := { zeta := false }) only [concatNats_cons]

  sorry

/-
1 - 0.52user 0.07system 0:00.59elapsed 100%CPU (0avgtext+0avgdata 259556maxresident)k
10 - 0.56user 0.05system 0:00.61elapsed 100%CPU (0avgtext+0avgdata 259796maxresident)k
20 - 0.58user 0.05system 0:00.64elapsed 100%CPU (0avgtext+0avgdata 259784maxresident)k
30 - 0.70user 0.07system 0:00.77elapsed 100%CPU (0avgtext+0avgdata 259780maxresident)k
40 - 0.86user 0.06system 0:00.92elapsed 100%CPU (0avgtext+0avgdata 259784maxresident)k
50 - 1.09user 0.08system 0:01.18elapsed 100%CPU (0avgtext+0avgdata 259716maxresident)k
60 - 1.43user 0.07system 0:01.51elapsed 100%CPU (0avgtext+0avgdata 259704maxresident)k
70 - 1.96user 0.08system 0:02.05elapsed 100%CPU (0avgtext+0avgdata 259636maxresident)k
80 - 2.54user 0.10system 0:02.64elapsed 100%CPU (0avgtext+0avgdata 259776maxresident)k
90 - 3.41user 0.08system 0:03.50elapsed 100%CPU (0avgtext+0avgdata 259868maxresident)k
100 - 4.39user 0.09system 0:04.49elapsed 100%CPU (0avgtext+0avgdata 260308maxresident)k
110 - 5.59user 0.11system 0:05.70elapsed 100%CPU (0avgtext+0avgdata 260308maxresident)k
120 - 6.98user 0.13system 0:07.12elapsed 99%CPU (0avgtext+0avgdata 259636maxresident)k
  - tactic 'simp' failed, nested error:
    (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use `set_option maxHeartbeats <num>` to set the limit) 
  - Where are the WHNFs that time out invoked? Can they be turned off?
  - maxHeartbeats := 1_000_000
130 - 8.82user 0.16system 0:08.99elapsed 99%CPU (0avgtext+0avgdata 259556maxresident)k
140 - 10.68user 0.18system 0:10.86elapsed 99%CPU (0avgtext+0avgdata 260032maxresident)k
150 - 13.03user 0.15system 0:13.19elapsed 99%CPU (0avgtext+0avgdata 269108maxresident)k
160 - 15.54user 0.19system 0:15.75elapsed 99%CPU (0avgtext+0avgdata 297368maxresident)k
  - maximum recursion depth has been reached (use `set_option maxRecDepth <num>` to increase limit)
  - maxRecDepth := 1024
170 - 18.52user 0.17system 0:18.70elapsed 99%CPU (0avgtext+0avgdata 330304maxresident)k
180 - 21.64user 0.18system 0:21.84elapsed 99%CPU (0avgtext+0avgdata 367492maxresident)k
190 - 25.25user 0.24system 0:25.51elapsed 99%CPU (0avgtext+0avgdata 416756maxresident)k
200 - 29.95user 0.22system 0:30.19elapsed 99%CPU (0avgtext+0avgdata 473124maxresident)k
	superlinear y = 0.000004x³ − 0.000030x² + 0.005085x + 0.48451
-/
