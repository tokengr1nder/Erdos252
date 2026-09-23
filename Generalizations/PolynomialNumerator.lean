import Generalizations.AffineNumerator
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Polynomial perturbations and proper-divisor examples

The difficult input is E252, strengthened in RobustTail and AffineNumerator.
Here the standard falling-factorial basis turns polynomial numerators into
rational multiples of the exponential series. Both numerator and denominator
can then be varied in one unconditional irrationality theorem.
-/

namespace Erdos252.Generalizations

open Filter Polynomial
open scoped BigOperators Topology ArithmeticFunction.sigma

noncomputable section

theorem geometric_one_eq_exp (c : ℤ) :
    (∑' n : ℕ, geometricTerm (fun _ => 1) c n) = Real.exp ((c : ℝ)⁻¹) := by
  rw [Real.exp_eq_exp_ℝ]
  simpa only [geometricTerm, Int.cast_one, one_div, inv_pow, div_eq_mul_inv,
    mul_inv_rev, mul_comm, mul_one] using
    (NormedSpace.expSeries_div_hasSum_exp ((c : ℝ)⁻¹)).tsum_eq

theorem hasSum_descFactorial_geometric (c : ℤ) (hc : c ≠ 0) (j : ℕ) :
    HasSum (fun n : ℕ => (n.descFactorial j : ℝ) /
      ((c : ℝ) ^ n * (n.factorial : ℝ)))
      ((c : ℝ)⁻¹ ^ j * ∑' n : ℕ, geometricTerm (fun _ => 1) c n) := by
  let f (n : ℕ) := (n.descFactorial j : ℝ) / ((c : ℝ) ^ n * (n.factorial : ℝ))
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have heq (n : ℕ) : f (n + j) = (c : ℝ)⁻¹ ^ j * geometricTerm (fun _ => 1) c n := by
    have hf : (n + j).factorial = n.factorial * (n + j).descFactorial j := by
      simpa only [Nat.add_sub_cancel] using
        (Nat.factorial_mul_descFactorial (show j ≤ n + j by omega)).symm
    have hd : ((n + j).descFactorial j : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr (show j ≤ n + j by omega)).ne'
    dsimp [f, geometricTerm]
    rw [hf, Nat.cast_mul, pow_add, inv_pow]
    push_cast
    field_simp
  have hs : HasSum (fun n => f (n + j))
      ((c : ℝ)⁻¹ ^ j * ∑' n, geometricTerm (fun _ => 1) c n) :=
    ((summable_geometric_one c).hasSum.mul_left _).congr_fun heq
  have hp : ∑ n ∈ Finset.range j, f n = 0 := Finset.sum_eq_zero fun n hn => by
    simp [f, Nat.descFactorial_of_lt (Finset.mem_range.mp hn)]
  simpa only [hp, zero_add] using hs.sum_range_add

/-- Every rational polynomial contributes only a rational multiple of exp(1/c). -/
theorem hasSum_polynomial_geometric (P : Polynomial ℚ) (c : ℤ) (hc : c ≠ 0) :
    ∃ r : ℚ, HasSum (fun n : ℕ => ((P.eval (n : ℚ) : ℚ) : ℝ) /
      ((c : ℝ) ^ n * (n.factorial : ℝ)))
      ((r : ℝ) * ∑' n : ℕ, geometricTerm (fun _ => 1) c n) := by
  let S : Polynomial.Sequence ℚ := ⟨descPochhammer ℚ, fun j => by
    rw [Polynomial.degree_eq_natDegree (monic_descPochhammer ℚ j).ne_zero,
      descPochhammer_natDegree]⟩
  have hspan : Submodule.span ℚ (Set.range S) = ⊤ :=
    S.span fun j => by
      change IsUnit (descPochhammer ℚ j).leadingCoeff
      rw [(monic_descPochhammer ℚ j).leadingCoeff]
      exact isUnit_one
  have hmem : P ∈ Submodule.span ℚ (Set.range S) := by rw [hspan]; trivial
  induction hmem using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨j, rfl⟩ := hp
    refine ⟨(c : ℚ)⁻¹ ^ j, ?_⟩
    simpa only [S, descPochhammer_eval_eq_descFactorial, Rat.cast_natCast,
      Rat.cast_pow, Rat.cast_inv, Rat.cast_intCast] using hasSum_descFactorial_geometric c hc j
  | zero => exact ⟨0, by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b, ?_⟩
    simpa only [Polynomial.eval_add, Rat.cast_add, add_div, add_mul] using ha.add hb
  | smul a p _ hp =>
    obtain ⟨b, hb⟩ := hp
    refine ⟨a * b, ?_⟩
    simpa only [Polynomial.eval_smul, smul_eq_mul, Rat.cast_mul, mul_div_assoc,
      mul_assoc] using hb.mul_left (a : ℝ)

theorem irrational_sigma_add_rational_exp {k : ℕ} (hk : 0 < k)
    (q : ℚ) (c : ℤ) (hc : c ≠ 0) :
    Irrational ((∑' n, (σ k n : ℝ) / ((c : ℝ) ^ n * (n.factorial : ℝ))) +
      (q : ℝ) * Real.exp ((c : ℝ)⁻¹)) := by
  have h := irrational_affine_sigma_geometric hk (q.den : ℤ) q.num c
    (by exact_mod_cast q.den_nz) hc
  have heq : (∑' n : ℕ, ((q.den : ℝ) * (σ k n : ℝ) + q.num) /
      ((c : ℝ) ^ n * (n.factorial : ℝ))) =
      (q.den : ℝ) * ((∑' n, (σ k n : ℝ) / ((c : ℝ) ^ n * (n.factorial : ℝ))) +
        (q : ℝ) * Real.exp ((c : ℝ)⁻¹)) := by
    have ht (n : ℕ) : ((q.den : ℝ) * (σ k n : ℝ) + q.num) /
        ((c : ℝ) ^ n * (n.factorial : ℝ)) =
        (q.den : ℝ) * geometricTerm (fun n => (σ k n : ℤ)) c n +
          (q.num : ℝ) * geometricTerm (fun _ => 1) c n := by
      simp only [geometricTerm, Int.cast_natCast, Int.cast_one]
      ring
    simp_rw [ht]
    rw [Summable.tsum_add ((summable_geometric_sigma k hc).mul_left _)
      ((summable_geometric_one c).mul_left _), tsum_mul_left, tsum_mul_left,
      geometric_one_eq_exp, Rat.cast_def]
    dsimp [geometricTerm]
    push_cast
    field_simp
  exact Irrational.of_natCast_mul q.den (heq ▸ (by simpa using h))

/-- Absolute convergence holds without a sign or nonvanishing condition on a. -/
theorem summable_polynomial_sigma_geometric (k : ℕ) (a : ℚ)
    (P : Polynomial ℚ) (c : ℤ) (hc : c ≠ 0) :
    Summable (fun n : ℕ => ((a : ℝ) * (σ k n : ℝ) + ((P.eval (n : ℚ) : ℚ) : ℝ)) /
      ((c : ℝ) ^ n * (n.factorial : ℝ))) := by
  obtain ⟨r, hr⟩ := hasSum_polynomial_geometric P c hc
  simpa only [geometricTerm, Int.cast_natCast, ← mul_div_assoc, ← add_div] using
    (((summable_geometric_sigma k hc).mul_left (a : ℝ)).add hr.summable)

/-- A joint extension: arbitrary rational polynomial perturbations, arbitrary
nonzero rational sigma coefficient, and any signed geometric-factorial base. -/
theorem irrational_polynomial_sigma_geometric {k : ℕ} (hk : 0 < k)
    (a : ℚ) (ha : a ≠ 0) (P : Polynomial ℚ) (c : ℤ) (hc : c ≠ 0) :
    Irrational (∑' n : ℕ, ((a : ℝ) * (σ k n : ℝ) + ((P.eval (n : ℚ) : ℚ) : ℝ)) /
      ((c : ℝ) ^ n * (n.factorial : ℝ))) := by
  obtain ⟨r, hr⟩ := hasSum_polynomial_geometric P c hc
  rw [geometric_one_eq_exp] at hr
  have hs := ((summable_geometric_sigma k hc).hasSum.mul_left (a : ℝ)).add hr
  have h := (irrational_sigma_add_rational_exp hk (r / a) c hc).ratCast_mul ha
  change Irrational ((a : ℝ) * ((∑' n, geometricTerm (fun n => (σ k n : ℤ)) c n) +
    ((r / a : ℚ) : ℝ) * Real.exp ((c : ℝ)⁻¹))) at h
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have heq : (a : ℝ) * ((∑' n, geometricTerm (fun n => (σ k n : ℤ)) c n) +
      ((r / a : ℚ) : ℝ) * Real.exp ((c : ℝ)⁻¹)) =
      (a : ℝ) * (∑' n, geometricTerm (fun n => (σ k n : ℤ)) c n) +
        (r : ℝ) * Real.exp ((c : ℝ)⁻¹) := by push_cast; field_simp
  rw [heq, ← hs.tsum_eq] at h
  simpa only [geometricTerm, Int.cast_natCast, ← mul_div_assoc, ← add_div] using h

/-- In particular, powers of proper divisors give another full family. -/
theorem proper_divisor_sum_eq {k : ℕ} (hk : 0 < k) (n : ℕ) :
    (∑ d ∈ n.divisors.erase n, (d : ℝ) ^ k) = (σ k n : ℝ) - (n : ℝ) ^ k := by
  by_cases hn : n = 0
  · simp [hn, zero_pow hk.ne']
  simp only [ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow]
  exact Finset.sum_erase_eq_sub (by simp [Nat.mem_divisors, hn])

theorem irrational_proper_divisors_geometric {k : ℕ} (hk : 0 < k)
    (c : ℤ) (hc : c ≠ 0) :
    Irrational (∑' n : ℕ, ((σ k n : ℝ) - (n : ℝ) ^ k) /
      ((c : ℝ) ^ n * (n.factorial : ℝ))) := by
  simpa [sub_eq_add_neg] using irrational_polynomial_sigma_geometric hk 1 one_ne_zero
    (-(Polynomial.X : Polynomial ℚ) ^ k) c hc

theorem irrational_proper_divisor_sum {k : ℕ} (hk : 0 < k) (c : ℤ) (hc : c ≠ 0) :
    Irrational (∑' n : ℕ, (∑ d ∈ n.divisors.erase n, (d : ℝ) ^ k) /
      ((c : ℝ) ^ n * (n.factorial : ℝ))) := by
  simp_rw [proper_divisor_sum_eq hk]
  exact irrational_proper_divisors_geometric hk c hc

theorem irrational_proper_divisors_double_factorial {k : ℕ} (hk : 0 < k) :
    Irrational (∑' n : ℕ, ((σ k n : ℝ) - (n : ℝ) ^ k) /
      ((2 * n).doubleFactorial : ℝ)) := by
  simpa [Nat.doubleFactorial_two_mul] using
    irrational_proper_divisors_geometric hk 2 (by decide)

theorem irrational_alternating_proper_double_factorial {k : ℕ} (hk : 0 < k) :
    Irrational (∑' n : ℕ, (-1 : ℝ) ^ n * ((σ k n : ℝ) - (n : ℝ) ^ k) /
      ((2 * n).doubleFactorial : ℝ)) := by
  have h := irrational_proper_divisors_geometric hk (-2) (by decide)
  convert h using 1
  apply tsum_congr
  intro n
  rw [Nat.doubleFactorial_two_mul]
  push_cast
  rw [show (-2 : ℝ) = (-1) * 2 by norm_num, mul_pow]
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow, inv_neg, inv_one]
  ring

theorem irrational_sigma_plus_square_example :
    Irrational (∑' n : ℕ, ((σ 5 n : ℝ) + (n : ℝ) ^ 2 + 1) /
      ((3 : ℝ) ^ n * (n.factorial : ℝ))) := by
  have h := irrational_polynomial_sigma_geometric (k := 5) (by decide)
    1 one_ne_zero ((Polynomial.X : Polynomial ℚ) ^ 2 + 1) 3 (by decide)
  convert h using 1
  apply tsum_congr
  intro n
  rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  push_cast
  ring

end

end Erdos252.Generalizations
