import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Summability of the factorial divisor-sum series

This file proves the analytic existence of the series in Erdős Problem 252
for every exponent.  The proof uses the elementary Mathlib bound
`σ k n ≤ n ^ (k + 1)` and domination by an exponential factorial series.
-/

open scoped Nat ArithmeticFunction.sigma

namespace Erdos252.Tail

lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := Nat.lt_two_pow_self.le

lemma pow_le_pow_pow (n d : ℕ) : n ^ d ≤ (2 ^ d) ^ n := by
  simpa only [← pow_mul, Nat.mul_comm] using
    Nat.pow_le_pow_left (nat_le_two_pow n) d

/-- Every fixed polynomial divided by `n!` is summable. -/
theorem summable_natPow_div_factorial (d : ℕ) :
    Summable (fun n : ℕ ↦ (n : ℝ) ^ d / (n ! : ℝ)) := by
  refine .of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
    (Real.summable_pow_div_factorial ((2 : ℝ) ^ d))
  gcongr
  exact_mod_cast pow_le_pow_pow n d

/-- The Erdős 252 factorial series is summable for every exponent `k`. -/
theorem summable_sigma_div_factorial (k : ℕ) :
    Summable (fun n : ℕ ↦ (ArithmeticFunction.sigma k n : ℝ) / (n ! : ℝ)) := by
  refine .of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
    (summable_natPow_div_factorial (k + 1))
  gcongr
  exact_mod_cast ArithmeticFunction.sigma_le_pow_succ k n

#print axioms nat_le_two_pow
#print axioms pow_le_pow_pow
#print axioms summable_natPow_div_factorial
#print axioms summable_sigma_div_factorial

end Erdos252.Tail
