#!/usr/bin/env python3
"""Translate the examples of Li, Passmore and Paulson (JAR 2019) from the Isabelle source
`Univ_RCF_Example.thy` into Lean files for the `smt` tactic and SMT-LIB files.

  scripts/gen_li_examples.py [THY] [OUTDIR] [N ...]

Defaults: the thy file under ~/Projects/cad-formalization/Wenda/Univariate_RCF, OUTDIR
li_examples, examples 1-7. The formulas are parsed (Isabelle syntax: \\<forall>/\\<exists>,
\\<not>, \\<and>/&, \\<or>/|, relations, + - * / ^ over one real variable x) and printed in both
languages from the same syntax tree, so both files state exactly the Isabelle formula.

- Powers are expanded into products: the `smt` tactic currently fails on `x ^ n` over Real, and
  SMT-LIB has no power operator.
- Universal examples: the Lean lemma is the formula for an arbitrary real x; the SMT-LIB file
  asserts its negation (status unsat).
- Existential examples: the Lean lemma is `∃ x : Real, φ`; the SMT-LIB file asserts φ, whose
  satisfiability is the statement (status sat). There is no unsat proof to check for these.
  For them the script also writes an unsat variant `LiEx<n>u`, NOT one of Li's examples: φ is a
  conjunction, and its last conjunct is replaced by its complement (p > 0 by p <= 0, etc.),
  which makes it unsatisfiable while keeping the same polynomials. The Lean lemma is ¬φ' for an
  arbitrary real x, the SMT-LIB file asserts φ' (status unsat). Meant only for comparing the
  fine-grained and the coarse reconstruction on these polynomials.
"""

COMPLEMENT = {"<": ">=", ">": "<=", "<=": ">", ">=": "<"}

def unsat_variant(f):
    """φ with its last conjunct complemented (see the module docstring)."""
    assert f[0] == "and" and f[1][-1][0] == "rel"
    last = f[1][-1]
    flipped = ("not", last) if last[1] == "=" else ("rel", COMPLEMENT[last[1]], last[2], last[3])
    return ("and", f[1][:-1] + [flipped])
import os, re, sys

THY = os.path.expanduser("~/Projects/cad-formalization/Wenda/Univariate_RCF/Univ_RCF_Example.thy")

def examples(src):
    out = {}
    for m in re.finditer(r'\(\*(.*?)\*\)\s*lemma example_(\d+):\s*"(.*?)"', src, re.S):
        out[int(m.group(2))] = (" ".join(m.group(1).split()), m.group(3))
    return out

TOKEN = re.compile(r"\\<forall>|\\<exists>|\\<not>|\\<and>|\\<or>|\\<ge>|\\<le>|::real|<=|>=|\d+|[a-z]+|[-+*/^()<>=&|.]")

def tokenize(s):
    ts = TOKEN.findall(s)
    norm = {"\\<and>": "&", "\\<or>": "|", "\\<ge>": ">=", "\\<le>": "<="}
    return [norm.get(t, t) for t in ts]

REL = {"<", ">", "<=", ">=", "="}
ARITH = {"+", "-", "*", "/", "^"}

class Parser:
    def __init__(self, ts):
        self.ts, self.i = ts, 0
    def peek(self, k=0):
        j = self.i + k
        return self.ts[j] if j < len(self.ts) else None
    def eat(self, t=None):
        tok = self.ts[self.i]
        if t is not None and tok != t:
            raise SyntaxError(f"expected {t}, got {tok} at {self.i}")
        self.i += 1
        return tok
    # formulas
    def formula(self):
        q = None
        if self.peek() in ("\\<forall>", "\\<exists>"):
            q = "forall" if self.eat() == "\\<forall>" else "exists"
            paren = self.peek() == "("          # both `x::real.` and `(x::real).` occur
            if paren: self.eat("(")
            self.eat("x"); self.eat("::real")
            if paren: self.eat(")")
            self.eat(".")
        return q, self.disj()
    def disj(self):
        fs = [self.conj()]
        while self.peek() == "|":
            self.eat(); fs.append(self.conj())
        return fs[0] if len(fs) == 1 else ("or", fs)
    def conj(self):
        fs = [self.neg()]
        while self.peek() == "&":
            self.eat(); fs.append(self.neg())
        return fs[0] if len(fs) == 1 else ("and", fs)
    def neg(self):
        if self.peek() == "\\<not>":
            self.eat(); return ("not", self.neg())
        return self.primary()
    def matching(self, j):
        depth = 0
        while True:
            if self.ts[j] == "(": depth += 1
            elif self.ts[j] == ")":
                depth -= 1
                if depth == 0: return j
            j += 1
    def primary(self):
        if self.peek() == "(":
            after = self.ts[self.matching(self.i) + 1] if self.matching(self.i) + 1 < len(self.ts) else None
            if after not in REL and after not in ARITH:
                self.eat("("); f = self.disj(); self.eat(")"); return f
        l = self.sum()
        op = self.eat()
        if op not in REL:
            raise SyntaxError(f"expected a relation, got {op}")
        return ("rel", op, l, self.sum())
    # terms
    def sum(self):
        e = self.prod()
        while self.peek() in ("+", "-"):
            op = self.eat(); e = ("add" if op == "+" else "sub", e, self.prod())
        return e
    def prod(self):
        e = self.unary()
        while self.peek() in ("*", "/"):
            op = self.eat(); e = ("mul" if op == "*" else "div", e, self.unary())
        return e
    def unary(self):
        if self.peek() == "-":
            self.eat(); return ("neg", self.unary())
        return self.power()
    def power(self):
        b = self.atom()
        if self.peek() == "^":
            self.eat(); return ("pow", b, int(self.eat()))
        return b
    def atom(self):
        t = self.eat()
        if t == "(":
            e = self.sum(); self.eat(")"); return e
        if t == "x": return ("var",)
        if t.isdigit(): return ("num", t)
        raise SyntaxError(f"unexpected {t}")

def lean(e):
    k = e[0]
    if k == "num": return e[1]
    if k == "var": return "x"
    if k == "neg": return f"(-{lean(e[1])})"
    if k == "pow": return "(" + " * ".join([lean(e[1])] * e[2]) + ")"
    if k in ("add", "sub", "mul", "div"):
        return f"({lean(e[1])} {dict(add='+', sub='-', mul='*', div='/')[k]} {lean(e[2])})"
    if k == "rel": return f"{lean(e[2])} {dict(zip(['<','>','<=','>=','='], ['<','>','≤','≥','=']))[e[1]]} {lean(e[3])}"
    if k == "not": return f"¬({lean(e[1])})"
    if k == "and": return "(" + " ∧\n      ".join(lean(f) for f in e[1]) + ")"
    if k == "or": return "(" + " ∨\n      ".join(lean(f) for f in e[1]) + ")"
    raise ValueError(k)

def smt(e):
    k = e[0]
    if k == "num": return e[1]
    if k == "var": return "x"
    if k == "neg": return f"(- {smt(e[1])})"
    if k == "pow": return "(* " + " ".join([smt(e[1])] * e[2]) + ")"
    if k in ("add", "sub", "mul", "div"):
        return f"({dict(add='+', sub='-', mul='*', div='/')[k]} {smt(e[1])} {smt(e[2])})"
    if k == "rel": return f"({e[1]} {smt(e[2])} {smt(e[3])})"
    if k == "not": return f"(not {smt(e[1])})"
    if k in ("and", "or"): return f"({k}\n    " + "\n    ".join(smt(f) for f in e[1]) + ")"
    raise ValueError(k)

HEADER = """/-!
Example {n} of Li, Passmore and Paulson, "Deciding univariate polynomial problems using untrusted
certificates in Isabelle/HOL" (JAR 2019), translated mechanically from `example_{n}` in
`Univ_RCF_Example.thy` (Isabelle `univ_rcf` development, Wenda Li) by
`scripts/gen_li_examples.py`. Timing recorded in the Isabelle file: {timing}.
Powers are written as products: the `smt` tactic currently fails on `x ^ n` over `Real`.
-/
"""

def main():
    args = sys.argv[1:]
    thy = args.pop(0) if args and args[0].endswith(".thy") else THY
    outdir = args.pop(0) if args and not args[0].isdigit() else "li_examples"
    wanted = [int(a) for a in args] or list(range(1, 8))
    os.makedirs(outdir, exist_ok=True)
    exs = examples(open(thy).read())
    for n in wanted:
        timing, text = exs[n]
        p = Parser(tokenize(text))
        q, f = p.formula()
        assert p.i == len(p.ts), f"example {n}: trailing tokens {p.ts[p.i:]}"
        if q == "exists":
            stmt = f"∃ x : Real,\n      {lean(f)}"
            sig = f"lemma li_example_{n} :\n    {stmt}"
        else:
            sig = f"lemma li_example_{n} (x : Real) :\n    {lean(f)}"
        leanfile = ("import Smt\nimport Smt.Real\n\n" + HEADER.format(n=n, timing=timing) +
                    f"\nset_option maxHeartbeats 4000000 in\n{sig} := by\n  smt\n\n#print axioms li_example_{n}\n")
        with open(os.path.join(outdir, f"LiEx{n}.lean"), "w") as fh:
            fh.write(leanfile)
        if q == "exists":
            note = (";; The lemma states: there is a real x satisfying the formula below; this file\n"
                    ";; asserts the formula, whose satisfiability is the statement (no unsat proof).\n")
            status, asserted = "sat", smt(f)
        else:
            note = (";; The lemma states: for all real x, the formula below holds; this file asserts\n"
                    ";; its negation, which is unsat.\n")
            status, asserted = "unsat", f"(not {smt(f)})"
        smtfile = (f";; Example {n} of Li, Passmore and Paulson, JAR 2019 (Univ_RCF_Example.thy, example_{n}).\n"
                   + note + ";; Translated mechanically from the Isabelle source by scripts/gen_li_examples.py.\n"
                   + f"(set-logic QF_NRA)\n(set-info :status {status})\n(declare-fun x () Real)\n"
                   + f"(assert {asserted})\n(check-sat)\n(exit)\n")
        with open(os.path.join(outdir, f"LiEx{n}.smt2"), "w") as fh:
            fh.write(smtfile)
        print(f"example {n}: {q or 'forall'}, status {status}")
        if q == "exists":
            v = unsat_variant(f)
            note = (f"Unsat variant of example {n}, NOT one of Li's examples: the last conjunct of the\n"
                    f"existential formula is replaced by its complement, which makes it unsatisfiable\n"
                    f"with the same polynomials. For comparing the fine-grained and the coarse\n"
                    f"reconstruction only.")
            leanv = ("import Smt\nimport Smt.Real\n\n/-!\n" + note + "\nGenerated by `scripts/gen_li_examples.py`"
                     " from `example_" + str(n) + "` in `Univ_RCF_Example.thy`.\n-/\n\n"
                     f"set_option maxHeartbeats 4000000 in\nlemma li_example_{n}u (x : Real) :\n    ¬{lean(v)} := by\n  smt\n\n"
                     f"#print axioms li_example_{n}u\n")
            with open(os.path.join(outdir, f"LiEx{n}u.lean"), "w") as fh:
                fh.write(leanv)
            smtv = ("".join(";; " + l + "\n" for l in note.split("\n"))
                    + ";; Generated by scripts/gen_li_examples.py.\n"
                    + f"(set-logic QF_NRA)\n(set-info :status unsat)\n(declare-fun x () Real)\n"
                    + f"(assert {smt(v)})\n(check-sat)\n(exit)\n")
            with open(os.path.join(outdir, f"LiEx{n}u.smt2"), "w") as fh:
                fh.write(smtv)
            print(f"example {n}u: unsat variant written")

if __name__ == "__main__":
    main()
