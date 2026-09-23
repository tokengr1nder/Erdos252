import Generalizations.WeightedTail

/-!
# Geometric factorial denominators

The weights in the factorial tail may have either sign. Bounded weights preserve
the original E252 error estimate; reciprocal integer powers also preserve the
integrality argument. No small-coefficient irrationality criterion is used.
-/

namespace Erdos252.Generalizations

open Filter
open scoped BigOperators Topology ArithmeticFunction.sigma

noncomputable section

def weightedBlockTail (k : ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' j : ℕ, w j * blockTerm k (n + 1) j

theorem summable_weightedBlock (k n : ℕ) (w : ℕ → ℝ)
    (hw : ∀ j, ‖w j‖ ≤ 1) : Summable (fun j => w j * blockTerm k (n + 1) j) :=
  (hasSum_blockTerm k (n + 1) (by omega)).summable.of_norm_bounded fun j => by
    rw [norm_mul, Real.norm_of_nonneg (blockTerm_nonneg _ _ _)]
    exact mul_le_of_le_one_left (blockTerm_nonneg _ _ _) (hw j)

theorem weightedBlock_error (k n : ℕ) (w : ℕ → ℝ) (hw : ∀ j, ‖w j‖ ≤ 1) :
    weightedBlockTail k w n - weightedExpansion k w n =
      (∑' r : ℕ, w (r + (k + 1)) * blockTerm k (n + 1) (r + (k + 1))) +
      ∑ j ∈ Finset.range (k + 1), w j * (σ k (n + (j + 1)) : ℝ) *
        stirlingErr j (k + 1) ((n + (j + 1) : ℕ) : ℝ) := by
  rw [weightedBlockTail, ← (summable_weightedBlock k n w hw).sum_add_tsum_nat_add (k + 1)]
  simp only [weightedExpansion, stirlingErr, stirlingPoly, descRecip_centered, blockTerm,
    Nat.add_right_comm n 1, Nat.add_assoc, Finset.mul_sum, mul_sub,
    Finset.sum_sub_distrib, mul_one_div]
  simp only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  ring

theorem weightedBlock_error_bound (k n : ℕ) (w : ℕ → ℝ)
    (hw : ∀ j, ‖w j‖ ≤ 1) (hn : k + 1 ≤ n) :
    ‖weightedBlockTail k w n - weightedExpansion k w n‖ ≤ tailErr k n := by
  rw [weightedBlock_error k n w hw, tailErr_eq]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact tsum_of_norm_bounded
      (((summable_nat_add_iff (k + 1)).2
        (hasSum_blockTerm k (n + 1) (by omega)).summable).hasSum)
      (fun r => by
        rw [norm_mul, Real.norm_of_nonneg (blockTerm_nonneg _ _ _)]
        exact mul_le_of_le_one_left (blockTerm_nonneg _ _ _) (hw _))
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    have he := (stirlingErr_bounds (k + 1) (k + 1) ((n + (j + 1) : ℕ) : ℝ)
      (by exact_mod_cast (show k + 1 ≤ n + (j + 1) by omega)) j
      (by have := Finset.mem_range.mp hj; omega)).1
    rw [mul_assoc, norm_mul, Real.norm_of_nonneg (mul_nonneg (by positivity) he)]
    exact mul_le_of_le_one_left (mul_nonneg (by positivity) he) (hw j)

theorem tendsto_weightedBlock_error (k : ℕ) (w : ℕ → ℝ) (hw : ∀ j, ‖w j‖ ≤ 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      (weightedBlockTail k w n - weightedExpansion k w n)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_tailErr_mul k)
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
  exact mul_le_mul_of_nonneg_left (weightedBlock_error_bound k n w hw hn) (by positivity)

def geometricTerm (a : ℕ → ℤ) (c : ℤ) (n : ℕ) : ℝ :=
  (a n : ℝ) / ((c : ℝ) ^ n * (n.factorial : ℝ))

def geometricTail (a : ℕ → ℤ) (c : ℤ) (n : ℕ) : ℝ :=
  ((c : ℝ) ^ n * (n.factorial : ℝ)) *
    ((∑' m, geometricTerm a c m) - ∑ m ∈ Finset.range (n + 1), geometricTerm a c m)

theorem reciprocal_pow_bound {c : ℤ} (hc : c ≠ 0) (n : ℕ) :
    ‖(c : ℝ)⁻¹ ^ n‖ ≤ 1 := by
  have h : (1 : ℝ) ≤ ‖(c : ℝ)‖ := by
    rw [Real.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast (show (1 : ℤ) ≤ |c| by have := abs_pos.mpr hc; omega)
  rw [norm_pow, norm_inv]
  exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h)

theorem summable_geometric_sigma (k : ℕ) {c : ℤ} (hc : c ≠ 0) :
    Summable (geometricTerm (fun n => (σ k n : ℤ)) c) :=
  (summable_sigma_factorial k).of_norm_bounded fun n => by
    rw [geometricTerm, Int.cast_natCast, mul_comm ((c : ℝ) ^ n), div_mul_eq_div_div, norm_div,
      Real.norm_of_nonneg (by positivity : 0 ≤ (σ k n : ℝ) / (n.factorial : ℝ)),
      div_eq_mul_inv, ← norm_inv, ← inv_pow]
    exact mul_le_of_le_one_right (by positivity) (reciprocal_pow_bound hc n)

theorem geometricPrefix_integral (a : ℕ → ℤ) (c : ℤ) (n : ℕ) :
    ∃ z : ℤ, ((c : ℝ) ^ n * (n.factorial : ℝ)) *
      (∑ m ∈ Finset.range (n + 1), geometricTerm a c m) = z := by
  by_cases hc : c = 0
  · subst c
    obtain rfl | hn := Nat.eq_zero_or_pos n
    · exact ⟨a 0, by simp [geometricTerm]⟩
    · exact ⟨0, by simp [zero_pow hn.ne']⟩
  refine ⟨∑ m ∈ Finset.range (n + 1),
    c ^ (n - m) * (n.factorial / m.factorial : ℕ) * a m, ?_⟩
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := by have := Finset.mem_range.mp hm; omega
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hpow : (c : ℝ) ^ n = (c : ℝ) ^ (n - m) * (c : ℝ) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hmn]
  rw [geometricTerm, Nat.cast_div (Nat.factorial_dvd_factorial hmn)
    (by positivity : (m.factorial : ℝ) ≠ 0), hpow]
  field_simp

theorem geometricTail_integral (a : ℕ → ℤ) (c : ℤ)
    (hr : ¬ Irrational (∑' n, geometricTerm a c n)) :
    ∀ᶠ n : ℕ in atTop, ∃ z : ℤ, geometricTail a c n = z := by
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hr
  filter_upwards [eventually_ge_atTop r.den] with n hn
  obtain ⟨d, hd⟩ := Nat.dvd_factorial r.pos hn
  obtain ⟨p, hp⟩ := geometricPrefix_integral a c n
  refine ⟨c ^ n * d * r.num - p, ?_⟩
  rw [geometricTail, mul_sub, hp, hr, Rat.cast_def, hd]
  push_cast
  field_simp

theorem hasSum_geometricBlock (a : ℕ → ℤ) {c : ℤ} (hc : c ≠ 0)
    (hs : Summable (geometricTerm a c)) (n : ℕ) :
    HasSum (fun j : ℕ => (c : ℝ)⁻¹ ^ (j + 1) * (a (n + (j + 1)) : ℝ) /
      ((n + 1).ascFactorial (j + 1) : ℝ)) (geometricTail a c n) := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  rw [geometricTail, ← hs.sum_add_tsum_nat_add (n + 1), add_sub_cancel_left]
  refine (((summable_nat_add_iff (n + 1)).2 hs).hasSum.mul_left _).congr_fun fun j => ?_
  rw [geometricTerm, Nat.add_comm j (n + 1),
    show n + 1 + j = n + (j + 1) by omega, pow_add,
    ← Nat.factorial_mul_ascFactorial n (j + 1), Nat.cast_mul]
  simp only [inv_pow]
  field_simp
  ring

theorem geometricTail_sigma (k : ℕ) {c : ℤ} (hc : c ≠ 0) (n : ℕ) :
    geometricTail (fun m => (σ k m : ℤ)) c n =
      weightedBlockTail k (fun j => (c : ℝ)⁻¹ ^ (j + 1)) n := by
  simpa only [weightedBlockTail, blockTerm, Int.cast_natCast, mul_div_assoc,
    Nat.add_right_comm n 1, Nat.add_assoc] using
    (hasSum_geometricBlock _ hc (summable_geometric_sigma k hc) n).tsum_eq.symm

/-- A signed geometric-factorial extension of E252 in every positive degree. -/
theorem irrational_sigma_geometric_factorial {k : ℕ} (hk : 0 < k)
    (c : ℤ) (hc : c ≠ 0) :
    Irrational (∑' n : ℕ, (σ k n : ℝ) / ((c : ℝ) ^ n * (n.factorial : ℝ))) := by
  by_contra hr
  have hint := geometricTail_integral (fun n => (σ k n : ℤ)) c hr
  simp_rw [geometricTail_sigma k hc] at hint
  exact weighted_tail_obstruction hk (fun j => (c : ℝ)⁻¹ ^ (j + 1))
    (weightedBlockTail k (fun j => (c : ℝ)⁻¹ ^ (j + 1)))
    (fun n => weightedBlockTail k (fun j => (c : ℝ)⁻¹ ^ (j + 1)) n -
      weightedExpansion k (fun j => (c : ℝ)⁻¹ ^ (j + 1)) n)
    (pow_ne_zero _ (inv_ne_zero (by exact_mod_cast hc)))
    (fun _ => (add_sub_cancel _ _).symm)
    (tendsto_weightedBlock_error k _ (fun j => reciprocal_pow_bound hc (j + 1))) hint

end

end Erdos252.Generalizations
