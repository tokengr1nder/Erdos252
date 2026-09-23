import Generalizations

/-! Independent, expanded statement checks for the joint generalizations. -/

namespace GeneralizationsAudit

open Erdos252.Generalizations Filter
open scoped BigOperators Topology

theorem joint_statement {a b : ℕ → ℤ} {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n)
    (hb : Summable (fun n => (b n : ℝ) / (∏ j ∈ Finset.range n, q j : ℕ)))
    (hr : Tendsto (fun n => ((a n - (q n : ℤ) * b n + b (n + 1) : ℤ) : ℝ) / q n)
      atTop (𝓝 0)) :
    Irrational (∑' n : ℕ, (a n : ℝ) / (∏ j ∈ Finset.range (n + 1), q j : ℕ)) ↔
      ¬ ∀ᶠ n in atTop, a n - (q n : ℤ) * b n + b (n + 1) = 0 :=
  irrational_joint_product_series_iff hq hb hr

theorem arbitrary_denominator_statement {a b : ℕ → ℤ} {D : ℕ → ℕ}
    (h0 : 0 < D 0) (hdiv : ∀ n, D n ∣ D (n + 1))
    (hg : ∀ n, 2 * D n ≤ D (n + 1))
    (hb : Summable (fun n => (b n : ℝ) / D n))
    (hr : Tendsto (fun n =>
      ((a n - ((D (n + 1) / D n : ℕ) : ℤ) * b n + b (n + 1) : ℤ) : ℝ) /
        (D (n + 1) / D n : ℕ)) atTop (𝓝 0))
    (hne : ¬ ∀ᶠ n in atTop, a n - ((D (n + 1) / D n : ℕ) : ℤ) * b n + b (n + 1) = 0) :
    Irrational (∑' n : ℕ, (a n : ℝ) / D (n + 1)) :=
  irrational_general_denominator h0 hdiv hg hb hr hne

theorem joint_series_summable {a b : ℕ → ℤ} {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n)
    (hb : Summable (fun n => (b n : ℝ) / (∏ j ∈ Finset.range n, q j : ℕ)))
    (hr : Tendsto (fun n => ((a n - (q n : ℤ) * b n + b (n + 1) : ℤ) : ℝ) / q n)
      atTop (𝓝 0)) :
    Summable (fun n : ℕ => (a n : ℝ) / (∏ j ∈ Finset.range (n + 1), q j : ℕ)) :=
  (hasSum_normalized hq a b hb (summable_cantor hq hr)).summable

theorem factorial_minus_one_is_not_a_divisibility_chain :
    ¬ (Nat.factorial 3 - 1) ∣ (Nat.factorial 4 - 1) := by decide

theorem polynomial_numerator_statement (k : ℕ) (hk : 0 < k)
    (a : ℚ) (ha : a ≠ 0) (P : Polynomial ℚ) (c : ℤ) (hc : c ≠ 0) :
    Irrational (∑' n : ℕ,
      ((a : ℝ) * (ArithmeticFunction.sigma k n : ℝ) + ((P.eval (n : ℚ) : ℚ) : ℝ)) /
        ((c : ℝ) ^ n * (n.factorial : ℝ))) :=
  irrational_polynomial_sigma_geometric hk a ha P c hc

theorem polynomial_series_summable (k : ℕ) (a : ℚ) (P : Polynomial ℚ)
    (c : ℤ) (hc : c ≠ 0) :
    Summable (fun n : ℕ =>
      ((a : ℝ) * (ArithmeticFunction.sigma k n : ℝ) + ((P.eval (n : ℚ) : ℚ) : ℝ)) /
        ((c : ℝ) ^ n * (n.factorial : ℝ))) :=
  summable_polynomial_sigma_geometric k a P c hc

theorem proper_divisors_statement (k : ℕ) (hk : 0 < k) (c : ℤ) (hc : c ≠ 0) :
    Irrational (∑' n : ℕ, ((ArithmeticFunction.sigma k n : ℝ) - (n : ℝ) ^ k) /
      ((c : ℝ) ^ n * (n.factorial : ℝ))) :=
  irrational_proper_divisors_geometric hk c hc

#print axioms Erdos252.erdos_252
#print axioms irrational_cantor_iff
#print axioms irrational_joint_product_series_iff
#print axioms irrational_general_denominator
#print axioms irrational_of_sigma_bound
#print axioms irrational_sigma_factorial_power
#print axioms irrational_sigma_quadratic_product
#print axioms irrational_alternating_sigma
#print axioms irrational_totient_factorial_squared
#print axioms irrational_oscillating_quadratic
#print axioms irrational_corrected_sigma_product
#print axioms irrational_corrected_sigma_factorial
#print axioms weighted_tail_obstruction
#print axioms telescoping_counterexample
#print axioms joint_statement
#print axioms arbitrary_denominator_statement
#print axioms joint_series_summable
#print axioms factorial_minus_one_is_not_a_divisibility_chain
#print axioms isolated_shift_not_tendsto_const
#print axioms weighted_tail_obstruction_of_limit
#print axioms irrational_sigma_geometric_factorial
#print axioms irrational_affine_sigma_geometric
#print axioms irrational_sigma_add_rational_exp
#print axioms irrational_polynomial_sigma_geometric
#print axioms irrational_proper_divisors_geometric
#print axioms irrational_proper_divisor_sum
#print axioms irrational_proper_divisors_double_factorial
#print axioms irrational_alternating_proper_double_factorial
#print axioms irrational_sigma_plus_square_example
#print axioms polynomial_numerator_statement
#print axioms polynomial_series_summable
#print axioms proper_divisors_statement

end GeneralizationsAudit
