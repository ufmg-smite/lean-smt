# SMT Lean
This project is inspired by [SMTCoq](https://smtcoq.github.io/) and aims to
provide Lean tactics that discharge goals into SMT solvers. This project is
in its early design/development phase and is not recommended for use.

# Requirements
`lean-smt` communicates with SMT solvers via the SMT-LIB textual interface.
Therefore, it requires a supported SMT solver to be installed. Currently,
`lean-smt` supports two SMT solvers:
- [`cvc5`](https://cvc5.github.io) (default).
- [`z3`](https://github.com/Z3Prover/z3).

# Usage
To use the `lean-smt` in your project. Add the following line to your list of
dependencies in `lakefile.lean`:
```lean
require smt from git "https://github.com/ufmg-smite/lean-smt.git"@"main"
```
`lean-smt` comes with one main tactic, `smt`, that translates the current goal
into an SMT query, sends the query to an SMT solver, and prints the result
returned by the SMT solver. The tactic DOES NOT currently generate a proof term
to discharge the goal.

# Example
To use the `smt` tactic, you just need to import the `Smt` library:
```lean
import Smt

theorem modus_ponens (p q : Prop) : p → (p → q) → q := by
  smt
  simp_all
```
For the theorem above, `smt` prints
```smt2
goal: p → (p → q) → q

query:
(declare-const p Bool)
(declare-const q Bool)
(assert (not (=> p (=> (=> p q) q))))
(check-sat)

result: unsat
```
You can specify the SMT solver to use like so:
```lean
set_option smt.solver.kind "z3"
```
`lean-smt` assumes the specified SMT solver to be in the path. If that's not
the case, you can specify the path to the SMT solver like so:
```lean
set_option smt.solver.path "path/to/z3"
```
