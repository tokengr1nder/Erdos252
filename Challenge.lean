module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Real.Irrational

public section

/-!
# Erdős problem 252: the statement of record

For every natural exponent `k`, the sum of `sigma k n / n!` over natural `n`
is irrational. Here `sigma k n` is Mathlib's sum of the `k`th powers of the
positive divisors of `n`. Its value at zero is zero, so this is the same series
as the usual positive-index formulation. The proved version is in
`Erdos252.Solution`; this independent Challenge deliberately has no proof.
-/

namespace Erdos252

/-- The complete factorial divisor-sum irrationality statement. -/
theorem erdos_252 (k : ℕ) :
    Irrational (∑' n : ℕ, (ArithmeticFunction.sigma k n : ℝ) / (n.factorial : ℝ)) := by
  sorry

end Erdos252
