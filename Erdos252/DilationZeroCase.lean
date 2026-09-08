import Erdos252.U5DilationGenericTail
import Erdos252.DilationGrowth
import Erdos252.EventuallyIntegral

/-!
# The zero-degree factorial divisor series

Degree zero is treated using positivity and decay of the actual scaled
factorial tail. No progression-mean assertion at degree zero is used.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Every positive-index actual scaled tail has a positive first term. -/
theorem genericScaledFullTail5_pos_of_pos (k n : ℕ) (hn : 0 < n) :
    0 < genericScaledFullTail5 k n := by
  rw [genericScaledFullTail5_eq_tsum_block k n hn]
  have hfirst : 0 < genericBlockTerm5 k n 0 := by
    simp only [genericBlockTerm5, Nat.ascFactorial_zero, Nat.ascFactorial_succ,
      Nat.add_zero, Nat.mul_one]
    exact div_pos (Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos k n hn.ne'))
      (Nat.cast_pos.mpr hn)
  exact hfirst.trans_le ((summable_genericBlockTerm5 k n hn).le_tsum 0
    (fun j _ => genericBlockTerm5_nonneg k n j))

/-- In degree zero the finite main term is just the first actual tail term. -/
theorem genericDilationTailMain5_zero_eq (n : ℕ) :
    genericDilationTailMain5 0 n =
      (ArithmeticFunction.sigma 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  simp [genericDilationTailMain5_eq_Icc]

/-- The elementary divisor-count square-root bound forces the zero-degree main
term to tend to zero. -/
theorem tendsto_genericDilationTailMain5_zero :
    Tendsto (genericDilationTailMain5 0) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n : ℕ =>
      64 * (Real.sqrt ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (tendsto_sqrt_nat_div_nat.comp (tendsto_add_atTop_nat 1)).const_mul 64
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro n
    rw [genericDilationTailMain5_zero_eq]
    positivity
  · intro n
    rw [genericDilationTailMain5_zero_eq]
    have hs := sigma_real_le_sixty_four_pow_sqrt 0 (n + 1) (Nat.succ_pos n)
    simp only [pow_zero, mul_one] at hs
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hs (by positivity)

/-- Each zero-degree block is dominated by one fixed geometric series. -/
theorem genericBlockTerm5_zero_le_geometric {n : ℕ} (hn : 4 ≤ n) (j : ℕ) :
    genericBlockTerm5 0 n j ≤
      (64 * Real.sqrt (n : ℝ) / (n : ℝ)) * (1 / 2 : ℝ) ^ j := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hj : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
  have hnj : n + j ≤ n * (2 ^ j) ^ 2 := by
    calc
      n + j ≤ n * (j + 1) := by nlinarith
      _ ≤ n * 2 ^ j := Nat.mul_le_mul_left n hj
      _ ≤ n * (2 ^ j) ^ 2 := Nat.mul_le_mul_left n (by nlinarith)
  have hnjR : ((n + j : ℕ) : ℝ) ≤ (n : ℝ) * ((2 : ℝ) ^ j) ^ 2 := by
    exact_mod_cast hnj
  have hsqrt : Real.sqrt ((n + j : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) * (2 : ℝ) ^ j := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    simpa only [mul_pow, Real.sq_sqrt hnR.le] using hnjR
  have hsigma : (ArithmeticFunction.sigma 0 (n + j) : ℝ) ≤
      64 * Real.sqrt (n : ℝ) * (2 : ℝ) ^ j := by
    have hs := sigma_real_le_sixty_four_pow_sqrt 0 (n + j) (by omega)
    simp only [pow_zero, mul_one] at hs
    exact hs.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 64))
  have hden : n * 4 ^ j ≤ n.ascFactorial (j + 1) := by
    calc
      n * 4 ^ j ≤ n * n ^ j := Nat.mul_le_mul_left n (Nat.pow_le_pow_left hn j)
      _ = n ^ (j + 1) := (pow_succ' n j).symm
      _ ≤ _ := Nat.pow_succ_le_ascFactorial n (j + 1)
  have hdenR : (n : ℝ) * (4 : ℝ) ^ j ≤ (n.ascFactorial (j + 1) : ℝ) := by
    exact_mod_cast hden
  unfold genericBlockTerm5
  calc
    _ ≤ (64 * Real.sqrt (n : ℝ) * (2 : ℝ) ^ j) / (n.ascFactorial (j + 1) : ℝ) :=
      div_le_div_of_nonneg_right hsigma (by positivity)
    _ ≤ (64 * Real.sqrt (n : ℝ) * (2 : ℝ) ^ j) / ((n : ℝ) * (4 : ℝ) ^ j) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdenR
    _ = _ := by
      rw [show (4 : ℝ) ^ j = (2 : ℝ) ^ j * (2 : ℝ) ^ j by rw [← mul_pow]; norm_num]
      rw [div_pow, one_pow]
      field_simp

/-- A direct bound on the actual zero-degree tail, independent of the generic
finite-expansion error estimates. -/
theorem genericScaledFullTail5_zero_le_sqrt {n : ℕ} (hn : 4 ≤ n) :
    genericScaledFullTail5 0 n ≤ 128 * Real.sqrt (n : ℝ) / (n : ℝ) := by
  have hnpos : 0 < n := by omega
  rw [genericScaledFullTail5_eq_tsum_block 0 n hnpos]
  calc
    _ ≤ ∑' j : ℕ, (64 * Real.sqrt (n : ℝ) / (n : ℝ)) * (1 / 2 : ℝ) ^ j :=
      (summable_genericBlockTerm5 0 n hnpos).tsum_le_tsum
        (genericBlockTerm5_zero_le_geometric hn) (summable_geometric_two.mul_left _)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_two]; ring

/-- The actual zero-degree scaled factorial tail tends to zero. -/
theorem tendsto_genericScaledFullTail5_zero :
    Tendsto (genericScaledFullTail5 0) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n : ℕ => 128 * Real.sqrt (n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using tendsto_sqrt_nat_div_nat.const_mul 128
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (genericScaledFullTail5_pos_of_pos 0 n (by omega)).le
  · filter_upwards [eventually_ge_atTop 4] with n hn
    exact genericScaledFullTail5_zero_le_sqrt hn

/-- The factorial divisor-count series is irrational. -/
theorem irrational_alpha_zero : Irrational (alpha 0) := by
  by_contra hx
  obtain ⟨N, hN⟩ := eventually_genericScaledFullTail5_integral 0 hx
  have hz := dilation5_eventually_zero_of_integral_tendsto
    tendsto_genericScaledFullTail5_zero ((eventually_ge_atTop N).mono hN)
  obtain ⟨n, hn, hnpos⟩ := (hz.and (eventually_ge_atTop 1)).exists
  exact (genericScaledFullTail5_pos_of_pos 0 n (by omega)).ne' hn

#print axioms genericScaledFullTail5_pos_of_pos
#print axioms genericDilationTailMain5_zero_eq
#print axioms tendsto_genericDilationTailMain5_zero
#print axioms genericBlockTerm5_zero_le_geometric
#print axioms genericScaledFullTail5_zero_le_sqrt
#print axioms tendsto_genericScaledFullTail5_zero
#print axioms irrational_alpha_zero

end

end Erdos252
