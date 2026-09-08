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
  have hsplit : (n + 1).ascFactorial (r + 1) *
      (n + 1 + (r + 1)).ascFactorial d =
      (n + 1).ascFactorial (r + d + 1) := by
    rw [Nat.ascFactorial_mul_ascFactorial]
    congr 1
    omega
  calc
    _ ≤ (d ^ d * (n + 1 + (r + 1)).ascFactorial d) *
        (n + 1).ascFactorial (r + 1) :=
      Nat.mul_le_mul hnum (Nat.pow_succ_le_ascFactorial _ _)
    _ = _ := by rw [← hsplit]; ring

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
  have hm : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hroot : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt hmR.le
  have hrootle : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt (m : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast hnm
  have hprod : Real.sqrt (m : ℝ) * Real.sqrt ((n : ℝ) + 1) ≤ m := by
    calc
      _ ≤ Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) :=
        mul_le_mul_of_nonneg_left hrootle (Real.sqrt_nonneg _)
      _ = _ := by nlinarith only [hsq]
  calc
    _ ≤ 64 * (m : ℝ) ^ k * Real.sqrt (m : ℝ) :=
      sigma_real_le_sixty_four_pow_sqrt k m hm
    _ ≤ (64 / Real.sqrt ((n : ℝ) + 1)) * (m : ℝ) ^ (k + 1) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hroot).mpr
      rw [pow_succ]
      have hh := mul_le_mul_of_nonneg_left hprod
        (show 0 ≤ 64 * (m : ℝ) ^ k by positivity)
      convert hh using 1 <;> ring

/-- Every omitted actual term obeys a fixed geometric majorant. -/
theorem genericDilationOmittedTerm5_le (k n r : ℕ) :
    genericBlockTerm5 k (n + 1) (r + (k + 1)) ≤
      (64 / Real.sqrt ((n : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ (k + 1) /
        ((n : ℝ) + 1) ^ (r + 1) := by
  have hden : (0 : ℝ) < ((n + 1).ascFactorial (r + (k + 1) + 1) : ℝ) := by
    exact_mod_cast Nat.ascFactorial_pos n _
  unfold genericBlockTerm5
  calc
    _ ≤ ((64 / Real.sqrt ((n : ℝ) + 1)) *
        ((n + 1 + (r + (k + 1)) : ℕ) : ℝ) ^ (k + 1)) /
          ((n + 1).ascFactorial (r + (k + 1) + 1) : ℝ) :=
      (div_le_div_iff_of_pos_right hden).mpr
        (dilation_sigma_le_pow_succ_div_sqrt k n _ (by omega))
    _ = (64 / Real.sqrt ((n : ℝ) + 1)) *
        (((n + 1 + (r + (k + 1)) : ℕ) : ℝ) ^ (k + 1) /
          ((n + 1).ascFactorial (r + (k + 1) + 1) : ℝ)) := by ring
    _ ≤ (64 / Real.sqrt ((n : ℝ) + 1)) *
        (((k + 1 : ℕ) : ℝ) ^ (k + 1) / ((n : ℝ) + 1) ^ (r + 1)) :=
      mul_le_mul_of_nonneg_left (dilation_polynomial_block_le (k + 1) n r (by omega))
        (by positivity)
    _ = _ := by ring

private theorem hasSum_dilation_geometric_reciprocal
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

theorem summable_dilation_geometric_reciprocal (C : ℝ) (n : ℕ) (hn : 0 < n) :
    Summable (fun r : ℕ => C / ((n : ℝ) + 1) ^ (r + 1)) :=
  (hasSum_dilation_geometric_reciprocal C n hn).summable

theorem tsum_dilation_geometric_reciprocal (C : ℝ) (n : ℕ) (hn : 0 < n) :
    (∑' r : ℕ, C / ((n : ℝ) + 1) ^ (r + 1)) = C / (n : ℝ) :=
  (hasSum_dilation_geometric_reciprocal C n hn).tsum_eq

theorem genericDilationOmittedTail5_le (k n : ℕ) (hn : 0 < n) :
    genericDilationOmittedTail5 k n (k + 1) ≤
      ((64 / Real.sqrt ((n : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)) / (n : ℝ) := by
  have hs : Summable (fun r : ℕ => genericBlockTerm5 k (n + 1) (r + (k + 1))) :=
    (summable_nat_add_iff (k + 1)).2 (summable_genericBlockTerm5 k (n + 1) (by omega))
  unfold genericDilationOmittedTail5
  calc
    _ ≤ ∑' r : ℕ,
        ((64 / Real.sqrt ((n : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)) /
          ((n : ℝ) + 1) ^ (r + 1) :=
      hs.tsum_le_tsum (genericDilationOmittedTerm5_le k n)
        (summable_dilation_geometric_reciprocal _ n hn)
    _ = _ := tsum_dilation_geometric_reciprocal _ n hn

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
#print axioms summable_dilation_geometric_reciprocal
#print axioms tsum_dilation_geometric_reciprocal
#print axioms genericDilationOmittedTail5_le
#print axioms genericDilationOmittedTail5_scaled_le

end Erdos252
