# Generalizing both functions

This is a separate Lean development. It does not change `Erdos252.erdos_252`
or the published proof. The main result below varies the numerator and the
denominator simultaneously, not just one at a time.

## Joint theorem

Choose arbitrary functions $a,b:\mathbb N\to\mathbb Z$ and
$D:\mathbb N\to\mathbb N$ satisfying

$$
D_0>0,\qquad D_n\mid D_{n+1},\qquad D_{n+1}\ge 2D_n.
$$

Set $q_n=D_{n+1}/D_n$ and

$$r_n=a_n-q_nb_n+b_{n+1}.$$

Assume $\sum_n |b_n|/D_n<\infty$ and $r_n/q_n\to0$. Then

$$
\sum_{n\ge0}\frac{a_n}{D_{n+1}}
\quad\hbox{is irrational if }r_n\ne0\hbox{ for infinitely many }n.
$$

This is `irrational_general_denominator` in [Denominator.lean](Denominator.lean).
The numerator can be negative, oscillatory, or nonmultiplicative. The denominator
need not be a factorial, a factorial power, or a polynomial product. Its precise
restriction here is the displayed positive divisibility-chain condition.
Taking $b=0$ gives the simpler small-coefficient criterion. Bounded $b$ always
satisfies the summability condition; unbounded $b$ is allowed when it does too.

In product form, $D_0=1$ and $D_{n+1}=\prod_{j=0}^n q_j$, the stronger theorem
`irrational_joint_product_series_iff` proves the **equivalence**:
irrationality holds exactly when $r$ is not eventually zero. It also proves
absolute convergence; no nonconvergent `tsum` is being used as a series value.

### Why it works

The identity

$$
\frac{a_n}{D_{n+1}}=
\frac{b_n}{D_n}-\frac{b_{n+1}}{D_{n+1}}+\frac{r_n}{D_{n+1}}
$$

removes a telescoping correction, whose sum is the rational number $b_0/D_0$.
For the remaining series, the scaled tail
$T_n=D_n\sum_{j\ge n}r_j/D_{j+1}$ tends to zero. If the sum were rational with
denominator $v$, then $vT_n$ would be an integer for every $n$, hence eventually
zero. The recurrence $q_nT_n=r_n+T_{n+1}$ would force $r_n$ eventually to vanish.

The restrictions cannot simply be dropped. For every integer $q_n\ge2$,

$$
\sum_{n\ge0}\frac{q_n-1}{\prod_{j=0}^n q_j}=1.
$$

This is the proved `telescoping_counterexample`, not just a numerical warning.

## Examples proved in Lean

Here $\sigma_k(m)=\sum_{d\mid m}d^k$ and $\varphi$ is Euler's totient function.
Every series in this list is proved irrational.

1. For every natural $k$:
   $$\sum_{m\ge0}\frac{\sigma_k(m)}{(m!)^{k+1}}.$$
2. A different arithmetic numerator and denominator:
   $$\sum_{n\ge0}\frac{\varphi(n+2)}{((n+2)!)^2}.$$
3. Alternating divisor sums, for every natural $k$:
   $$\sum_{n\ge0}\frac{(-1)^n\sigma_k(n+2)}{((n+2)!)^{k+1}}.$$
4. Both functions changed, with an oscillatory numerator:
   $$\sum_{n\ge0}
   \frac{\sigma_1(n+2)+(-1)^n((n+2)^2+2)}
        {\prod_{j=0}^n((j+2)^2+1)}.$$
   Here $q_n=(n+2)^2+1$ and $b_n=(-1)^n$, so the residual is exactly
   $\sigma_1(n+2)$. The numerator/base ratio itself does **not** tend to zero.
5. More generally, for arbitrary integer bases $q_n\ge(n+2)^{k+1}$ and any
   bounded integer sequence $b$:
   $$\sum_{n\ge0}
   \frac{\sigma_k(n+2)+q_nb_n-b_{n+1}}{\prod_{j=0}^n q_j}.$$
   No monotonicity or multiplicativity of $q$ or $b$ is required.

There is also a numerator-only extension preserving the original difficult
factorial denominator: for every natural $k$ and bounded integer $b$,

$$\sum_{n\ge0}
\frac{\sigma_k(n+2)+(n+2)b_n-b_{n+1}}{(n+2)!}
$$

is irrational. This uses the existing all-degree Erdős 252 theorem, rather than
pretending that the small-coefficient criterion covers that theorem for $k\ge1$.

`irrational_of_sigma_bound` further permits **any** integer numerator $a$ with
$|a_n|\le C\sigma_k(n+2)$, provided it is not eventually zero and the product
bases are at least $(n+2)^{k+1}$. The examples are instances, not the whole scope.

## What is classical, and what remains open?

The small-coefficient criterion is classical Oppenheim theory. See Theorem 2.1
of Hančl and Tijdeman, [On the irrationality of polynomial Cantor series](https://pub.math.leidenuniv.nl/~tijdemanr/hancti17.pdf).
The telescoping extension is an elementary consequence formalized here.
We make **no claim of a new irrationality criterion or a newly solved open
problem** for these examples.

Two nearby problems are not solved by this development:

- [Erdős 68](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/68.lean)
  asks about $\sum_{n\ge2}1/(n!-1)$. These denominators are not a divisibility
  chain: $3!-1=5$ does not divide $4!-1=23$ (also checked in `Audit.lean`).
- [Erdős 249](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/249.lean)
  asks about $\sum\varphi(n)/2^n$. The totient example above has a different
  denominator. In fact, bounded bases cannot give an irrationality instance of
  the small-residual criterion: an integer residual with $r_n/q_n\to0$ must then
  eventually vanish. No correction can evade that restriction when $q_n=2$.

Both catalogue entries are marked open at the time of review, 22 September 2026.
[Erdős 258](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/258.lean),
about the divisor-count function with general product bases tending to infinity,
is already marked solved in that catalogue. We neither claim it as a new solution
nor import a proof of it. These links document status, not dependencies of our Lean proof.

For harder extensions near the original factorial denominator,
[WeightedTail.lean](WeightedTail.lean) generalizes the cancellation argument to
arbitrary fixed shift weights, with a nonzero final weight. Its theorem explicitly
requires a suitable expansion with error $o(1/n)$ and rules out eventual integral
tails. Establishing such an expansion for a new numerator/denominator pair is
still a separate obligation. It is not an unconditional theorem for arbitrary
multiplicative functions or arbitrary deformations of $n!$.

## Source map and verification

- `Cantor.lean`: signed integer coefficients, convergence, exact rationality criterion.
- `Joint.lean`: telescoping normalization, joint classification, corrected families.
- `Denominator.lean`: direct formulation for arbitrary denominator functions.
- `Examples.lean`, `Instances.lean`: explicit arithmetic and oscillating examples.
- `WeightedTail.lean`: weighted version of the original cancellation obstruction.
- `Audit.lean`: independently expanded statements and axiom reports.

Run all commands from the **repository root**, using its pinned Lean toolchain:

```sh
lake --wfail build Erdos252 Generalizations
lake env lean --trust=0 audit/Statement.lean
lake env lean --trust=0 Generalizations/Audit.lean
lake env leanchecker --fresh --verbose Generalizations
```

On the configured Windows workstation, `Generalizations/Verify.ps1` additionally
recompiles every project proof module into a new directory at trust zero, audits
against those fresh files, and replays their kernels. It runs at idle CPU priority,
rejects diagnostics and nonstandard axioms, and checks that source hashes remain
unchanged during verification. Logs and a receipt go under `.lake/build/`.
It does not modify the original publication manifest or commit/push anything.
