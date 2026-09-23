# Genuine extensions of the E252 argument

This development keeps the difficult divisor-sum cancellation from E252.
It does not replace it with a classical small-coefficient criterion, and it
does not change the original `Erdos252.erdos_252` theorem or its source.

## One theorem, both functions changed

For **every** positive integer $k$, nonzero rational number $a$, rational
polynomial $P$, and nonzero integer $c$,

$$
\boxed{\displaystyle
\sum_{n\ge0}\frac{a\,\sigma_k(n)+P(n)}{c^n n!}\text{ is irrational}.}
$$

Here $\sigma_k(n)=\sum_{d\mid n}d^k$ for $n>0$, with $\sigma_k(0)=0$.
The degree and coefficients of $P$ are unrestricted. Negative $c$ gives
alternating series. Absolute convergence is proved as well.
There are no conjectural assumptions or unproved analytic hypotheses in this
theorem: `irrational_polynomial_sigma_geometric` in
[PolynomialNumerator.lean](PolynomialNumerator.lean).

The numerator need not be positive or multiplicative. The denominators here
are specifically $c^n n!$, not arbitrary sequences. Omitting the $n=0$ term
only subtracts the rational number $P(0)$.

## Examples that are easy to recognize

Every row below is an explicit Lean theorem, not a proposed application.

| Example | What changed |
| --- | --- |
| $\displaystyle\sum_{n\ge0}\frac{\sigma_k(n)-n^k}{c^n n!}$, $k\ge1$, $c\ne0$ | Replace all divisors by **proper divisors**. |
| $\displaystyle\sum_{n\ge0}\frac{\sigma_k(n)-n^k}{(2n)!!}$, $k\ge1$ | Proper divisors and the **even double factorial**. |
| $\displaystyle\sum_{n\ge0}\frac{(-1)^n(\sigma_k(n)-n^k)}{(2n)!!}$, $k\ge1$ | The alternating version is irrational too. |
| $\displaystyle\sum_{n\ge0}\frac{\sigma_5(n)+n^2+1}{3^n n!}$ | A nonmultiplicative numerator and a new denominator together. |

For $n>0$, $\sigma_k(n)-n^k=\sum_{d\mid n,\ d<n}d^k$.
For example, the numerator at $n=6$, $k=5$ is $1^5+2^5+3^5$.
Also $(2n)!!=2\cdot4\cdots(2n)=2^n n!$; the $n=0$ empty product is $1$.

These are consequences of a single theorem, not separate irrationality tricks.
The proper-divisor numerator is usually not multiplicative, which illustrates
why multiplicativity of the final numerator is not required.

## Why the extension works

1. Replacing $n!$ by $c^n n!$ weights the successive scaled-tail terms by
   $c^{-1},c^{-2},\ldots$. Their absolute values are at most one, so the E252
   remainder estimates survive, including negative $c$.
2. Rationality would still make sufficiently late scaled tails integers.
   The original dilation grid cancels the large terms as before.
3. The fresh-prime argument is stronger than originally needed: its surviving
   divisor expression cannot converge to **any constant**, not just zero.
   Two refined progressions give different limiting means.
4. Consequently a constant numerator perturbation is allowed. Its scaled tail
   has a finite limit, which the strengthened contradiction handles.
5. Every rational polynomial contributes a rational multiple of $e^{1/c}$.
   Mathlib's falling-factorial polynomial basis and a series reindexing reduce
   arbitrary $P$ to the constant-perturbation case.

In particular the development proves, for every rational $q$,

$$
\sum_{n\ge0}\frac{\sigma_k(n)}{c^n n!}+q e^{1/c}
\quad\text{is irrational}\qquad(k\ge1,\ c\in\mathbb Z\setminus\{0\}).
$$

This is stronger than just adding a rational number to E252: the perturbation
$q e^{1/c}$ is generally irrational itself.

## What would be a genuinely broader arithmetic theorem?

A natural next target is

$$F_P(n)=\sum_{d\mid n}P(d),$$

for a nonzero rational polynomial $P$ with $P(0)=0$. For example,
$P(X)=X^5+X^2$ gives $F_P(n)=\sigma_5(n)+\sigma_2(n)$.
This is **not** the polynomial perturbation already proved above: $P(n)$ and
$\sum_{d\mid n}P(d)$ are different functions.

Proving irrationality for all such $F_P(n)/n!$ would be equivalent to proving
that $1,\alpha_1,\ldots,\alpha_r$ are rationally linearly independent for every
$r$, where $\alpha_j=\sum\sigma_j(n)/n!$. That remains a research target here,
not a theorem in this directory. Deajim and Siksek's
[2011 paper](https://www.sciencedirect.com/science/article/pii/S0022314X11000102)
gives a criterion conditional on Schinzel's hypothesis, checked through $r=50$;
[Pratt's introduction](https://arxiv.org/html/2209.11124) records that distinction.

Other natural next directions are Jordan totients
$J_k(n)=n^k\prod_{p\mid n}(1-p^{-k})$, and product denominators
$\prod_{j=1}^n(aj+b)$ such as odd double factorials. These would require new
verified progression-mean identities or denominator expansions. They are
**candidates, not proved instances**, and are not asserted to be open problems
merely because this directory does not prove them.

Literature was checked on 22 September 2026. No new named open-problem solution
is claimed by this extension, and no priority claim is made for every individual
example. The all-degree joint theorem is a genuine extension of the verified
E252 argument. Classical fast-denominator results are retained separately in
[CLASSICAL.md](CLASSICAL.md), not presented as the main research result.

## Lean source and verification

- `WeightedTail.lean`: original weighted cancellation framework.
- `RobustTail.lean`: exclusion of every constant limit.
- `FactorialWeights.lean`: signed geometric tails, convergence, and integrality.
- `AffineNumerator.lean`: integer affine changes of the numerator.
- `PolynomialNumerator.lean`: the joint theorem, convergence, and explicit examples.
- `Audit.lean`: independently expanded statements and axiom reports.

From the repository root:

```sh
lake --wfail build Erdos252 Generalizations
lake env lean --trust=0 audit/Statement.lean
lake env lean --trust=0 Generalizations/Audit.lean
lake env leanchecker --fresh --verbose Generalizations
```

On the configured Windows workstation, `Generalizations/Verify.ps1` also
recompiles every project proof module into a fresh directory at trust zero,
checks statements and axioms against those files, and runs a fresh kernel replay.
The headline theorems use exactly `propext`, `Classical.choice`, and `Quot.sound`.
Source hashes must remain unchanged during verification; receipts and logs go
under `.lake/build/`. The script does not commit or push anything.
