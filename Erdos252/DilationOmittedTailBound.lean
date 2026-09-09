import Erdos252.U5DilationGenericTail
import Erdos252.DilationGrowth

/-!
# A geometric majorant for the actual omitted factorial tail

The final `d` ascending factors absorb a degree-`d` numerator. The remaining
factors give a geometric series. The square-root divisor bound then gives
the required decay after multiplication by the common tail index.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

theorem dilation_polynomial_ascending_bound (d n r : ℕ) (hd : 0 < d) :
    (n + 1 + (r + d)) ^ d * (n + 1) ^ (r + 1) ≤
      d ^ d * (n + 1).ascFactorial (r + d + 1) := by
  have hlin : n + 1 + (r + d) ≤ d * (n + 1 + (r + 1)) := by
    have hh : 0 ≤ (d - 1) * (n + r + 1) := Nat.zero_le _
    have hdd : d - 1 + 1 = d := by omega
    nlinarith
  have hnum : (n + 1 + (r + d)) ^ d ≤
      d ^ d * (n + 1 + (r + 1)).ascFactorial d := by
    calc
      _ ≤ (d * (n + 1 + (r + 1))) ^ d := Nat.pow_le_pow_left hlin d
      _ = d ^ d * (n + 1 + (r + 1)) ^ d := Nat.mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_succ_le_ascFactorial _ _)
  calc
    _ ≤ (d ^ d * (n + 1 + (r + 1)).ascFactorial d) *
        (n + 1).ascFactorial (r + 1) :=
      Nat.mul_le_mul hnum (Nat.pow_succ_le_ascFactorial _ _)
    _ = _ := by
      rw [mul_assoc, Nat.mul_comm ((n + 1 + (r + 1)).ascFactorial d),
        Nat.ascFactorial_mul_ascFactorial, Nat.add_right_comm r 1 d]

theorem dilation_polynomial_block_le (d n r : ℕ) (hd : 0 < d) :
    ((n + 1 + (r + d) : ℕ) : ℝ) ^ d /
        ((n + 1).ascFactorial (r + d + 1) : ℝ) ≤
      (d : ℝ) ^ d / ((n : ℝ) + 1) ^ (r + 1) := by
  have hden : (0 : ℝ) < ((n + 1).ascFactorial (r + d + 1) : ℝ) := by
    exact_mod_cast Nat.ascFactorial_pos n (r + d + 1)
  apply (div_le_div_iff₀ hden (by positivity)).mpr
  exact_mod_cast dilation_polynomial_ascending_bound d n r hd

theorem dilation_sigma_le_pow_succ_div_sqrt (k n m : ℕ)
    (hnm : n + 1 ≤ m) :
    (ArithmeticFunction.sigma k m : ℝ) ≤
      (64 / Real.sqrt ((n : ℝ) + 1)) * (m : ℝ) ^ (k + 1) := by
  calc
    _ ≤ 64 * (m : ℝ) ^ k * Real.sqrt (m : ℝ) :=
      sigma_real_le_sixty_four_pow_sqrt k m (by omega)
    _ = 64 * (m : ℝ) ^ (k + 1) / Real.sqrt (m : ℝ) := by
      simp only [pow_succ, mul_assoc, mul_div_assoc, Real.div_sqrt]
    _ ≤ 64 * (m : ℝ) ^ (k + 1) / Real.sqrt ((n : ℝ) + 1) := by
      gcongr
      exact_mod_cast hnm
    _ = _ := by ring

/-- Every omitted actual term obeys a fixed geometric majorant. -/
theorem genericDilationOmittedTerm5_le (k n r : ℕ) :
    genericBlockTerm5 k (n + 1) (r + (k + 1)) ≤
      (64 / Real.sqrt ((n : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ (k + 1) /
        ((n : ℝ) + 1) ^ (r + 1) := by
  unfold genericBlockTerm5
  refine (div_le_div_of_nonneg_right
    (dilation_sigma_le_pow_succ_div_sqrt k n _ (by omega)) (Nat.cast_nonneg _)).trans ?_
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (dilation_polynomial_block_le (k + 1) n r (by omega))
      (show 0 ≤ (64 : ℝ) / Real.sqrt ((n : ℝ) + 1) by positivity)

theorem hasSum_dilation_geometric_reciprocal
    (C : ℝ) (n : ℕ) (hn : 0 < n) :
    HasSum (fun r : ℕ => C / ((n : ℝ) + 1) ^ (r + 1)) (C / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : (1 : ℝ) / ((n : ℝ) + 1) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  convert! HasSum.mul_left (C / ((n : ℝ) + 1))
    (hasSum_geometric_of_lt_one (by positivity) hq) using 1
  · funext r
    simp only [pow_succ, div_eq_mul_inv, mul_inv_rev]
    ring
  · field_simp [hnR.ne']
    ring

theorem genericDilationOmittedTail5_le (k n : ℕ) (hn : 0 < n) :
    genericDilationOmittedTail5 k n (k + 1) ≤
      ((64 / Real.sqrt ((n : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)) / (n : ℝ) := by
  have hs : Summable (fun r : ℕ => genericBlockTerm5 k (n + 1) (r + (k + 1))) :=
    (summable_nat_add_iff (k + 1)).2 (summable_genericBlockTerm5 k (n + 1) (by omega))
  simpa only [genericDilationOmittedTail5, (hasSum_dilation_geometric_reciprocal _ n hn).tsum_eq] using
    hs.tsum_le_tsum (genericDilationOmittedTerm5_le k n)
      (hasSum_dilation_geometric_reciprocal _ n hn).summable

/-- The actual omitted tail is negligible after scaling by the base index. -/
theorem genericDilationOmittedTail5_scaled_le (k n : ℕ) (hn : 0 < n) :
    ((n : ℝ) + 1) * genericDilationOmittedTail5 k n (k + 1) ≤
      128 * ((k + 1 : ℕ) : ℝ) ^ (k + 1) / Real.sqrt ((n : ℝ) + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hratio : ((n : ℝ) + 1) / (n : ℝ) ≤ 2 :=
    (div_le_iff₀ hnR).mpr (by linarith)
  calc
    _ ≤ ((n : ℝ) + 1) *
        (((64 / Real.sqrt ((n : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)) /
          (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (genericDilationOmittedTail5_le k n hn) (by positivity)
    _ = (((n : ℝ) + 1) / (n : ℝ)) *
        ((64 / Real.sqrt ((n : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)) := by ring
    _ ≤ 2 * ((64 / Real.sqrt ((n : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by ring

#print axioms dilation_polynomial_ascending_bound
#print axioms dilation_polynomial_block_le
#print axioms dilation_sigma_le_pow_succ_div_sqrt
#print axioms genericDilationOmittedTerm5_le
#print axioms hasSum_dilation_geometric_reciprocal
#print axioms genericDilationOmittedTail5_le
#print axioms genericDilationOmittedTail5_scaled_le

end Erdos252
