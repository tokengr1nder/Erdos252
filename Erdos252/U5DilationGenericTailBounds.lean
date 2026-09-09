import Erdos252.U5DilationGenericTail
import Erdos252.DilationGrowth
import Erdos252.DilationOmittedTailBound

/-!
# Smallness of the generic factorial-tail expansion error

The elementary square-root divisor bound handles every exponent, including
zero and one. All estimates refer to the actual errors of the generic tail
expansion.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

private theorem genericDilation_sqrt_shift_bound5 (n h : ℕ)
    (hh : h ≤ n + 1) :
    Real.sqrt ((n + h : ℕ) : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) + 1) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
  have hhR : (h : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hh
  push_cast
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

/-- Every finite denominator remainder has a square-root numerator and two
full denominator powers remaining. -/
theorem genericDilationFiniteError5_term_bound (k n j : ℕ)
    (hn : k + 1 ≤ n) (hj : j < k + 1) :
    0 ≤ (ArithmeticFunction.sigma k (n + (j + 1)) : ℝ) *
        genericDilationError5 (j + 1) (k + 1) ((n + (j + 1) : ℕ) : ℝ) ∧
      (ArithmeticFunction.sigma k (n + (j + 1)) : ℝ) *
        genericDilationError5 (j + 1) (k + 1) ((n + (j + 1) : ℕ) : ℝ) ≤
          128 * ((k : ℝ) + 1) ^ (k + 1) * Real.sqrt ((n : ℝ) + 1) /
            ((n : ℝ) + 1) ^ 2 := by
  have hx : (0 : ℝ) < ((n + (j + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n + (j + 1) by omega)
  have hXx : (n : ℝ) + 1 ≤ ((n + (j + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show n + 1 ≤ n + (j + 1) by omega)
  have he := genericDilationError5_bounds (k + 1) (k + 1)
    ((n + (j + 1) : ℕ) : ℝ)
    (by exact_mod_cast (show k + 1 ≤ n + (j + 1) by omega))
    (j + 1) (by omega) (by omega)
  have hs := sigma_real_le_sixty_four_pow_sqrt k (n + (j + 1)) (by omega)
  have hroot := genericDilation_sqrt_shift_bound5 n (j + 1) (by omega)
  refine ⟨mul_nonneg (Nat.cast_nonneg _) he.1, ?_⟩
  calc
    _ ≤ (64 * ((n + (j + 1) : ℕ) : ℝ) ^ k *
          Real.sqrt ((n + (j + 1) : ℕ) : ℝ)) *
        (((k + 1 : ℕ) : ℝ) ^ (k + 1) /
          ((n + (j + 1) : ℕ) : ℝ) ^ (k + 1 + 1)) :=
      mul_le_mul hs he.2 he.1 (by positivity)
    _ = 64 * ((k : ℝ) + 1) ^ (k + 1) *
        Real.sqrt ((n + (j + 1) : ℕ) : ℝ) /
          ((n + (j + 1) : ℕ) : ℝ) ^ 2 := by
      rw [show k + 1 + 1 = k + 2 by omega, pow_add]
      push_cast
      field_simp
      ring
    _ ≤ 64 * ((k : ℝ) + 1) ^ (k + 1) *
        (2 * Real.sqrt ((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2 := by gcongr
    _ = _ := by ring

/-- The whole finite error, multiplied by the actual index plus one, is
bounded by a fixed multiple of `sqrt(n+1)/(n+1)`. -/
theorem genericDilationFiniteError5_bounds (k n : ℕ) (hn : k + 1 ≤ n) :
    0 ≤ genericDilationFiniteError5 k n ∧
      ((n : ℝ) + 1) * genericDilationFiniteError5 k n ≤
        128 * ((k : ℝ) + 1) ^ (k + 2) * (Real.sqrt ((n : ℝ) + 1) / ((n : ℝ) + 1)) := by
  have hX : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold genericDilationFiniteError5
  have hb := Finset.sum_le_sum (s := Finset.range (k + 1)) (fun j hj =>
    (genericDilationFiniteError5_term_bound k n j hn (Finset.mem_range.mp hj)).2)
  refine ⟨Finset.sum_nonneg (fun j hj =>
    (genericDilationFiniteError5_term_bound k n j hn (Finset.mem_range.mp hj)).1), ?_⟩
  convert! mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (n : ℝ) + 1) using 1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  field_simp

theorem tendsto_genericDilationFiniteError5_mul (k : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * genericDilationFiniteError5 k n)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => 128 * ((k : ℝ) + 1) ^ (k + 2) *
      (Real.sqrt ((n : ℝ) + 1) / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_zero] using
      (tendsto_sqrt_nat_div_nat.comp (tendsto_add_atTop_nat 1)).const_mul
        (128 * ((k : ℝ) + 1) ^ (k + 2))
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    exact mul_nonneg (by positivity) (genericDilationFiniteError5_bounds k n hn).1
  · filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    exact (genericDilationFiniteError5_bounds k n hn).2

/-- The actual omitted infinite tail vanishes even after multiplication by
the base index plus one. -/
theorem tendsto_genericDilationOmittedTail5_mul (k : ℕ) :
    Tendsto (fun n : ℕ =>
      ((n : ℝ) + 1) * genericDilationOmittedTail5 k n (k + 1))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ =>
      128 * ((k + 1 : ℕ) : ℝ) ^ (k + 1) / Real.sqrt ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one,
      Real.sqrt_div_self', mul_one_div, mul_zero] using
      (tendsto_sqrt_nat_div_nat.comp (tendsto_add_atTop_nat 1)).const_mul
        (128 * ((k + 1 : ℕ) : ℝ) ^ (k + 1))
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall (fun n =>
      mul_nonneg (by positivity) (genericDilationOmittedTail5_nonneg k n (k + 1)))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact genericDilationOmittedTail5_scaled_le k n (by omega)

/-- The error in the expansion of the actual factorial-series tail is
`o(1/(n+1))`, for every nonnegative divisor-sum exponent. -/
theorem tendsto_genericDilationTailError5_mul (k : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * genericDilationTailError5 k n)
      atTop (𝓝 0) := by
  simpa only [← mul_add, ← genericDilationTailError5_eq, add_zero] using
    (tendsto_genericDilationOmittedTail5_mul k).add (tendsto_genericDilationFiniteError5_mul k)

theorem tendsto_genericDilationTailError5 (k : ℕ) :
    Tendsto (genericDilationTailError5 k) atTop (𝓝 0) := by
  simpa only [mul_div_cancel_left₀ _ (Nat.cast_add_one_ne_zero (R := ℝ) _)] using
    (tendsto_genericDilationTailError5_mul k).div_atTop
    (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ)))

#print axioms genericDilation_sqrt_shift_bound5
#print axioms genericDilationFiniteError5_term_bound
#print axioms genericDilationFiniteError5_bounds
#print axioms tendsto_genericDilationFiniteError5_mul
#print axioms tendsto_genericDilationOmittedTail5_mul
#print axioms tendsto_genericDilationTailError5_mul
#print axioms tendsto_genericDilationTailError5

end Erdos252
