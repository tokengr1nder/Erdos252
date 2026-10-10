# Erdős 252: irrationality of the factorial divisor-sum series

Author: **Tokengrinder**

This source-only Lean development proves the statement of [Erdős Problem 252](https://www.erdosproblems.com/252) for every natural exponent:

```lean
theorem Erdos252.erdos_252 (k : ℕ) :
    Irrational (∑' n : ℕ,
      (ArithmeticFunction.sigma k n : ℝ) / (n.factorial : ℝ))
```

See [the proof outline](PROOF.md), the [complete typeset proof](PROOF.pdf)
([LaTeX source](PROOF.tex)), [verification details](VERIFICATION.md), and the
[Palomar submission account](PALOMAR.md), including provenance and AI involvement.
The complete Lean proof is in [Erdos252/Solution.lean](Erdos252/Solution.lean).
The PDF includes statements and proofs of every named lemma and theorem in
that module, including private lemmas, plus its definitions and the statement audit.

## Reproduce

Install Git and Elan. Use the exact Lean **4.35.0-rc2** toolchain in
[lean-toolchain](lean-toolchain) and keep [lake-manifest.json](lake-manifest.json)
unchanged so that all dependency revisions match.

```sh
git clone --branch publication/palomar-e252 https://github.com/tokengr1nder/Erdos252.git
cd Erdos252
lake exe cache get
lake build Erdos252
lake env lean --trust=0 audit/Statement.lean
```

For the exact artifact reviewed by Palomar, check out the immutable commit in
its verification report before running the Lake commands; the branch may advance.
The dependency revision is Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

These commands build the proof and check the [statement audit](audit/Statement.lean)
at Lean trust level zero. The audit checks the published statement, the divisor-sum
definition, summability, and the equivalent positive-index series. The required
main-theorem axiom output is:

```text
'Erdos252.erdos_252' depends on axioms: [propext, Classical.choice, Quot.sound]
```

For an additional replay of the imported logical declarations in a fresh
environment using Lean's own kernel, run:

```sh
lake env leanchecker --fresh --verbose Erdos252.Solution
```

This is an additional verification step, not a separate kernel implementation.

The proof development contains no incomplete proof placeholders. The separate
[Challenge](Challenge.lean) contains only the deliberate statement placeholder
used by Palomar's [Comparator configuration](comparator.json); the completed
proof does not import it. [formalization.yaml](formalization.yaml) records the
theorem, scope, sources, license, authorship, automation, and review status.

Palomar's own verification additionally compares the Challenge and Solution and
replays the proof with its required kernels. The reproduction commands above
do not by themselves assert that Palomar has accepted or registered a submission.

To typeset the complete proof locally, install Tectonic and run from the repository root:

```sh
tectonic PROOF.tex
```
