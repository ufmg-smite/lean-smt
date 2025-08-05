# Lean-SMT

This project provides Lean tactics to discharge goals into SMT solvers.
It is under active development and is currently in a beta phase. While it is
usable, it is important to note that there are still some rough edges and
ongoing improvements being made.

## Supported Theories
`lean-smt` currently supports the theories of Uninterpreted Functions and Linear
Integer/Real Arithmetic with quantifiers. Mathlib is required for Real
Arithmetic. Support for the theory of Bitvectors is at an experimental stage.
Support for additional theories is in progress.

## Requirements
`lean-smt` depends on [`lean-cvc5`](https://github.com/abdoo8080/lean-cvc5),
which currently only supports Linux and macOS.

## Setup
To use `lean-smt` in your project, add the following lines to your list of
dependencies in `lakefile.toml`:
```toml
[[require]]
name = "smt"
scope = "ufmg-smite"
rev = "main"
```
If your build configuration is in `lakefile.lean`, add the following line to
your dependencies:
```lean
require smt from git "https://github.com/ufmg-smite/lean-smt.git" @ "main"
```

## Usage
`lean-smt` comes with one main tactic, `smt`, that translates the current goal
into an SMT query, sends the query to cvc5, and (if the solver returns `unsat`)
replays cvc5's proof in Lean. cvc5's proofs may contain holes, returned as Lean
goals. You can fill these holes manually or with other tactics. To use the `smt`
tactic, you just need to import the `Smt` library:
```lean
import Smt

example [Nonempty U] {f : U → U → U} {a b c d : U}
  (h0 : a = b) (h1 : c = d) (h2 : p1 ∧ True) (h3 : (¬ p1) ∨ (p2 ∧ p3))
  (h4 : (¬ p3) ∨ (¬ (f a c = f b d))) : False := by
  smt [h0, h1, h2, h3, h4]
```
To use the `smt` tactic on Real arithmetic goals, import `Smt.Real`:
```lean
import Smt
import Smt.Real

example (ε : Real) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε := by
  smt [h1]
```
`lean-smt` integrates with
[`lean-auto`](https://github.com/leanprover-community/lean-auto) to provide
basic hammer-like capabilities. To set the `smt` tactic as a backend for `auto`,
import `Smt.Auto` and set `auto.native` to `true`:
```lean
import Mathlib.Algebra.Group.Defs
import Smt
import Smt.Auto

attribute [rebind Auto.Native.solverFunc] Smt.smtSolverFunc

set_option auto.native true

variable [Group G]

theorem inverse : ∀ (a : G), a * a⁻¹ = 1 := by
  auto [mul_assoc, one_mul, inv_mul_cancel]

theorem identity : ∀ (a : G), a * 1 = a := by
  auto [mul_assoc, one_mul, inv_mul_cancel, inverse]

theorem unique_identity : ∀ (e : G), (∀ a, e * a = a) ↔ e = 1 := by
  auto [mul_assoc, one_mul, inv_mul_cancel]
```
