# Palomar submission account

Responsible author and maintainer: **Tokengrinder**
([GitHub: tokengr1nder](https://github.com/tokengr1nder)).
The repository license is [GPL-3.0-only](LICENSE).

## The result being submitted

The one declaration selected by [comparator.json](comparator.json) is
`Erdos252.erdos_252`:

```lean
theorem erdos_252 (k : ℕ) :
    Irrational (∑' n : ℕ, (ArithmeticFunction.sigma k n : ℝ) / (n.factorial : ℝ))
```

For every natural exponent `k`, the sum of `sigma_k(n) / n!` is irrational,
where `sigma_k(n)` is the sum of the `k`th powers of the positive divisors of
`n`. The theorem has no number-theoretic hypotheses. Its intended axiom list
is exactly `propext`, `Classical.choice`, and `Quot.sound`.

[Erdős problem 252](https://www.erdosproblems.com/252) asks the positive-exponent
case. This theorem additionally covers exponent zero. Mathlib gives the
divisor sum at zero the value zero, so starting the series at zero does not
change its value. The [statement audit](audit/Statement.lean) explicitly checks
the divisor-sum definition, convergence, and the series starting at one.
Thus the totalized infinite-sum notation is not being used to bypass convergence.

There is no restriction to a finite set of exponents, conditional
prime-pattern assumption, or finite computational surrogate. The result does
not assert transcendence, independence of different sums, or irrationality for
other numerator or denominator functions.

## Mathematical provenance and contribution

This repository is the substantive proof development, not a wrapper around
another proof repository. The all-exponent argument was developed here and is
explained in [PROOF.md](PROOF.md) and [PROOF.pdf](PROOF.pdf), with
[PROOF.tex](PROOF.tex) as the latter's source. These are expositions of the Lean
proof, not independent verification artifacts.

The problem catalogue supplies the target and historical context.
[Pratt's paper](https://arxiv.org/abs/2209.11124) proves the exponent-four case
and describes earlier results. It is cited as background, not as a source of
this proof. No claim of endorsement by Pratt or the problem catalogue is made.
The original-proof classification in [formalization.yaml](formalization.yaml)
identifies the all-exponent theorem as an original result of this formalization.
It does not claim novelty for the conjecture, every special case, or
every ingredient, and it is not a claim that the literature search is exhaustive.

The [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/252.lean)
is related work. The file inspected during submission preparation records
statements and proof placeholders; it is not imported by this development.
The proof imports checked Mathlib material rather than those placeholders.

The argument has four main steps:

1. Rationality makes sufficiently late factorial-scaled tails integral.
   A finite Stirling expansion has an error small enough even after one
   additional scaling by the progression parameter.
2. The Chinese remainder theorem aligns a fixed finite grid of pairwise
   coprime dilations. Exact finite differences cancel the unwanted polynomial
   orders. The multipliers need not be prime.
3. An integer tending to zero is eventually zero. The error estimate then
   forces a finite signed combination of shifted normalized divisor sums
   to tend to zero along an arithmetic progression.
4. A shift with a nonzero coefficient is isolated by two refinements using a
   fresh prime. Their actual progression means differ by a nonzero quantity,
   contradicting the alleged zero limit. Exponent zero instead follows from
   positivity and decay of its factorial tail.

## Production and review

Tokengrinder directed the mathematical target, proof obligations, reviews,
compression, exposition, and publication. AI agents made substantive
mathematical and Lean contributions, including proof construction, debugging,
refactoring, and documentation. The workflow used OpenAI Codex agents and a
separate Claude/Opus agent. Exact model versions, complete prompt logs,
per-agent contributions, total costs, and total elapsed time were not
consistently recorded; no precise values are asserted retrospectively.

Separate agent review passes checked the result and its presentation under
user direction. This is **not a claim of independent human expert review or
peer review**. Mechanical checking and editorial review are distinct: a Lean
build or kernel replay checks a formal proof, while the statement audit and
the Palomar Challenge help check which proposition is being proved.
The current verification record belongs in [VERIFICATION.md](VERIFICATION.md).

## Submission boundary

[Challenge.lean](Challenge.lean) repeats the main statement using standard
Mathlib definitions. Its deliberate placeholder is used only to state the
comparison target. The completed proof in
[Erdos252/Solution.lean](Erdos252/Solution.lean) does not import the Challenge.
The Comparator configuration selects only `Erdos252.erdos_252` and permits
only the three standard axioms listed above. This submission concerns E252
alone; no other research result is included in its claim.

The submitted immutable commit must pass the full build, statement and axiom
audits, fresh kernel replay, and Palomar's mechanical verification. A reusable
Palomar preflight run is not itself a registry submission or registration.
Palomar's automated editorial review is also not human peer review.
