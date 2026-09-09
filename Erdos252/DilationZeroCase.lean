import Erdos252.U5DilationGenericTailBounds
import Erdos252.EventuallyIntegral

/-!
# The zero-degree factorial divisor series

Degree zero is treated using positivity and decay of the actual scaled
factorial tail. No progression-mean assertion at degree zero is used.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

/-- Every positive-index actual scaled tail has a positive first term. -/
theorem genericScaledFullTail5_pos_of_pos (k n : ℕ) (hn : 0 < n) :
    0 < genericScaledFullTail5 k n := by
  rw [genericScaledFullTail5_eq_tsum_block k n hn]
  refine lt_of_lt_of_le ?_ ((summable_genericBlockTerm5 k n hn).le_tsum 0
    (fun j _ => genericBlockTerm5_nonneg k n j))
  simp only [genericBlockTerm5, Nat.ascFactorial_zero, Nat.ascFactorial_succ,
    Nat.add_zero, Nat.mul_one]
  exact div_pos (Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos k n hn.ne'))
    (Nat.cast_pos.mpr hn)

/-- The elementary divisor-count square-root bound forces the zero-degree main
term to tend to zero. -/
theorem tendsto_genericDilationTailMain5_zero :
    Tendsto (genericDilationTailMain5 0) atTop (𝓝 0) := by
  have hmain (n : ℕ) : genericDilationTailMain5 0 n =
      (ArithmeticFunction.sigma 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
    simp [genericDilationTailMain5_eq_Icc]
  have hupper : Tendsto (fun n : ℕ =>
      64 * (Real.sqrt ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (tendsto_sqrt_nat_div_nat.comp (tendsto_add_atTop_nat 1)).const_mul 64
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => ?_) (fun n => ?_)
  · rw [hmain]
    positivity
  · rw [hmain]
    have hs := sigma_real_le_sixty_four_pow_sqrt 0 (n + 1) (Nat.succ_pos n)
    simp only [pow_zero, mul_one] at hs
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hs (by positivity)

/-- The actual zero-degree scaled factorial tail tends to zero. -/
theorem tendsto_genericScaledFullTail5_zero :
    Tendsto (genericScaledFullTail5 0) atTop (𝓝 0) := by
  refine (tendsto_add_atTop_iff_nat 1).mp ?_
  simpa only [genericDilationTail5_expansion, add_zero] using
    tendsto_genericDilationTailMain5_zero.add (tendsto_genericDilationTailError5 0)

/-- The factorial divisor-count series is irrational. -/
theorem irrational_alpha_zero : Irrational (alpha 0) := by
  by_contra hx
  obtain ⟨N, hN⟩ := eventually_genericScaledFullTail5_integral 0 hx
  have hz := dilation5_eventually_zero_of_integral_tendsto
    tendsto_genericScaledFullTail5_zero ((eventually_ge_atTop N).mono hN)
  obtain ⟨n, hn, hnpos⟩ := (hz.and (eventually_ge_atTop 1)).exists
  exact (genericScaledFullTail5_pos_of_pos 0 n (by omega)).ne' hn

#print axioms genericScaledFullTail5_pos_of_pos
#print axioms tendsto_genericDilationTailMain5_zero
#print axioms tendsto_genericScaledFullTail5_zero
#print axioms irrational_alpha_zero

end Erdos252
