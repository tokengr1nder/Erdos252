import Generalizations.FactorialWeights
import Generalizations.RobustTail

/-!
# Changing the numerator and denominator together

For every positive k and integers A, B, c with A and c nonzero, the series
with numerator A sigma_k(n) + B and denominator c^n n! is irrational.
The constant B is not a telescoping correction: its sum is B exp(1/c).
-/

namespace Erdos252.Generalizations

open Filter
open scoped BigOperators Topology ArithmeticFunction.sigma

noncomputable section

theorem summable_geometric_one (c : ℤ) : Summable (geometricTerm (fun _ => 1) c) := by
  change Summable (fun n => geometricTerm (fun _ => 1) c n)
  simpa only [geometricTerm, Int.cast_one, inv_pow, one_div, div_eq_mul_inv, mul_inv_rev,
    mul_comm, mul_one] using Real.summable_pow_div_factorial ((c : ℝ)⁻¹)

theorem tendsto_geometric_one_tail {c : ℤ} (hc : c ≠ 0) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * geometricTail (fun _ => 1) c n)
      atTop (𝓝 (c : ℝ)⁻¹) := by
  let R (n : ℕ) := ∑' j : ℕ,
    (c : ℝ)⁻¹ ^ (j + 2) / ((n + 1).ascFactorial (j + 2) : ℝ)
  have hs (n : ℕ) : HasSum (fun j : ℕ =>
      (c : ℝ)⁻¹ ^ (j + 1) / ((n + 1).ascFactorial (j + 1) : ℝ))
      (geometricTail (fun _ => 1) c n) := by
    simpa using hasSum_geometricBlock _ hc (summable_geometric_one c) n
  have hsplit (n : ℕ) : geometricTail (fun _ => 1) c n =
      (c : ℝ)⁻¹ / ((n : ℝ) + 1) + R n := by
    rw [← (hs n).tsum_eq, ← (hs n).summable.sum_add_tsum_nat_add 1]
    simp [R, Nat.ascFactorial_succ, Nat.add_assoc]
  have hbound (n : ℕ) : ‖R n‖ ≤ omittedTail 0 n 1 := by
    refine tsum_of_norm_bounded
      (((summable_nat_add_iff 1).2
        (hasSum_blockTerm 0 (n + 1) (by omega)).summable).hasSum) fun j => ?_
    simp only [blockTerm, norm_div, Real.norm_natCast, Nat.add_assoc]
    refine div_le_div_of_nonneg_right ((reciprocal_pow_bound hc (j + 2)).trans ?_)
      (Nat.cast_nonneg _)
    exact_mod_cast Nat.succ_le_of_lt
      (ArithmeticFunction.sigma_pos 0 (n + (1 + (j + 1))) (by omega))
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * omittedTail 0 n 1)
      atTop (𝓝 0) := by
    simpa [tailErr_eq, finiteErr, stirlingErr, stirlingPoly, descRecip_one] using
      tendsto_tailErr_mul 0
  have hR : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * R n) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by
      rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
      exact mul_le_mul_of_nonneg_left (hbound n) (by positivity)) hlim
  have heq (n : ℕ) : ((n : ℝ) + 1) * geometricTail (fun _ => 1) c n =
      (c : ℝ)⁻¹ + ((n : ℝ) + 1) * R n := by rw [hsplit, mul_add]; field_simp
  simpa only [heq, add_zero] using tendsto_const_nhds.add hR

theorem geometricTerm_affine (k : ℕ) (A B c : ℤ) (n : ℕ) :
    geometricTerm (fun m => A * (σ k m : ℤ) + B) c n =
      (A : ℝ) * geometricTerm (fun m => (σ k m : ℤ)) c n +
        (B : ℝ) * geometricTerm (fun _ => 1) c n := by
  simp only [geometricTerm, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast]
  ring

theorem summable_geometric_affine (k : ℕ) (A B c : ℤ) (hc : c ≠ 0) :
    Summable (geometricTerm (fun n => A * (σ k n : ℤ) + B) c) := by
  change Summable (fun n => geometricTerm (fun m => A * (σ k m : ℤ) + B) c n)
  simp_rw [geometricTerm_affine]
  exact ((summable_geometric_sigma k hc).mul_left _).add
    ((summable_geometric_one c).mul_left _)

theorem geometricTail_affine (k : ℕ) (A B c : ℤ) (hc : c ≠ 0) (n : ℕ) :
    geometricTail (fun m => A * (σ k m : ℤ) + B) c n =
      (A : ℝ) * geometricTail (fun m => (σ k m : ℤ)) c n +
        (B : ℝ) * geometricTail (fun _ => 1) c n := by
  unfold geometricTail
  simp_rw [geometricTerm_affine, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Summable.tsum_add ((summable_geometric_sigma k hc).mul_left _)
    ((summable_geometric_one c).mul_left _), tsum_mul_left, tsum_mul_left]
  ring

/-- Both functions vary. In particular, the numerator need not be multiplicative. -/
theorem irrational_affine_sigma_geometric {k : ℕ} (hk : 0 < k)
    (A B c : ℤ) (hA : A ≠ 0) (hc : c ≠ 0) :
    Irrational (∑' n : ℕ, ((A : ℝ) * (σ k n : ℝ) + B) /
      ((c : ℝ) ^ n * (n.factorial : ℝ))) := by
  by_contra hr
  let w (j : ℕ) := (c : ℝ)⁻¹ ^ (j + 1)
  let E (n : ℕ) := (A : ℝ) * (weightedBlockTail k w n - weightedExpansion k w n) +
    (B : ℝ) * geometricTail (fun _ => 1) c n
  have hint := geometricTail_integral (fun n => A * (σ k n : ℤ) + B) c
    (by simpa only [geometricTerm, Int.cast_add, Int.cast_mul, Int.cast_natCast] using hr)
  have hT (n : ℕ) : geometricTail (fun m => A * (σ k m : ℤ) + B) c n =
      weightedExpansion k (fun j => (A : ℝ) * w j) n + E n := by
    have hscale : weightedExpansion k (fun j => (A : ℝ) * w j) n =
        (A : ℝ) * weightedExpansion k w n := by
      simp only [weightedExpansion, Finset.mul_sum, mul_div_assoc, mul_assoc]
    rw [geometricTail_affine k A B c hc, geometricTail_sigma k hc, hscale]
    change (A : ℝ) * weightedBlockTail k w n + (B : ℝ) * geometricTail (fun _ => 1) c n =
      (A : ℝ) * weightedExpansion k w n + E n
    dsimp [E]
    ring
  have hE : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * E n)
      atTop (𝓝 ((B : ℝ) * (c : ℝ)⁻¹)) := by
    have h := ((tendsto_weightedBlock_error k w
      (fun j => reciprocal_pow_bound hc (j + 1))).const_mul (A : ℝ)).add
      ((tendsto_geometric_one_tail hc).const_mul (B : ℝ))
    simpa only [E, mul_add, mul_left_comm, mul_zero, zero_add] using h
  exact weighted_tail_obstruction_of_limit hk _ _ E
    (mul_ne_zero (by exact_mod_cast hA) (pow_ne_zero _ (inv_ne_zero (by exact_mod_cast hc))))
    hT _ hE hint

end

end Erdos252.Generalizations
