import Erdos252.RationalFactorial
import Erdos252.Tail

/-!
# Factorial divisor-sum series

The common series definitions and summability theorem are independent of
the historical six-term arithmetic reduction. The degree-five definitions
are retained here so their original names remain available to both routes.
-/

open scoped Nat ArithmeticFunction.sigma

namespace Erdos252

/-- The factorial divisor-sum series.  Its `n = 0` term is zero. -/
noncomputable def alpha (k : ℕ) : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.sigma k n : ℝ) / (n ! : ℝ)

/-- The `k = 5` series in Erdős Problem 252. -/
noncomputable def alpha5 : ℝ := alpha 5

/-- The sum of the terms strictly before `n`. -/
noncomputable def prefix5 (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, (ArithmeticFunction.sigma 5 m : ℝ) / (m ! : ℝ)

/-- The full tail starting at `n`, scaled by `(n - 1)!`. -/
noncomputable def scaledFullTail5 (n : ℕ) : ℝ :=
  ((n - 1).factorial : ℝ) * (alpha5 - prefix5 n)

/-- The series defining `alpha k` is summable. -/
theorem hasSum_alpha (k : ℕ) :
    HasSum (fun n : ℕ ↦ (ArithmeticFunction.sigma k n : ℝ) / (n ! : ℝ)) (alpha k) :=
  (Tail.summable_sigma_div_factorial k).hasSum

#print axioms hasSum_alpha

end Erdos252
