# SMT Lean
This project is inspired by [SMTCoq](https://smtcoq.github.io/) and aims to
provide Lean tactics that discharge goals into SMT solvers. It is under active
development and is currently in a beta phase. While it is ready for use, it is
important to note that there are still some rough edges and ongoing improvements
being made.

## Supported Theories
`lean-smt` currently supports the theories of Uninterpreted Functions and Linear
Integer/Real Arithmetic with quantifiers. Mathlib is currently required for
Arithmetic. Support for the theory of Bitvectors is at an experimental stage. We
are working on adding support for other theories as well.

## Requirements
`lean-smt` depends on [`lean-cvc5`](https://github.com/abdoo8080/lean-cvc5) FFI,
which currently only supports Linux.

## Usage
To use `lean-smt` in your project, add the following line to your list of
dependencies in `lakefile.lean`:
```lean
require smt from git "https://github.com/ufmg-smite/lean-smt.git"@"main"
```
`lean-smt` comes with one main tactic, `smt`, that translates the current goal
into an SMT query, sends the query to cvc5, and (if the solver returns `unsat`)
replays cvc5's proof in Lean. cvc5's proofs sometimes contain holes, which are
sent back to the user as Lean goals. The user can then fill in these holes
manually or by using other tactics.

### Example
To use the `smt` tactic, you just need to import the `Smt` library:
```lean
import Smt

example {U : Type} [Nonempty U] {f : U → U → U} {a b c d : U}
  (h0 : a = b) (h1 : c = d) (h2 : p1 ∧ True) (h3 : (¬ p1) ∨ (p2 ∧ p3))
  (h4 : (¬ p3) ∨ (¬ (f a c = f b d))) : False := by
  smt [h0, h1, h2, h3, h4]
```
