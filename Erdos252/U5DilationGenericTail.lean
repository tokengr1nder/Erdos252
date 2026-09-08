import Erdos252.FactorialSeries
import Erdos252.U5DilationGenericDenominator

/-!
# Actual factorial tails for arbitrary divisor-sum exponent

The definitions below use the original `alpha k` series. Rationality gives
eventual integrality, and the finite Stirling block has an exact decomposition
with the actual infinite tail. No irrationality assertion is made here.
-/

namespace Erdos252

open scoped BigOperators ArithmeticFunction.sigma

/-- The actual factorial-series prefix, excluding the term at `n`. -/
noncomputable def genericPrefix5 (k n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, (ArithmeticFunction.sigma k m : ℝ) / (m.factorial : ℝ)

/-- The actual factorial tail starting at `n`, scaled by `(n-1)!`. -/
noncomputable def genericScaledFullTail5 (k n : ℕ) : ℝ :=
  ((n - 1).factorial : ℝ) * (alpha k - genericPrefix5 k n)

/-- One actual ascending-factorial term in the scaled tail. -/
noncomputable def genericBlockTerm5 (k n j : ℕ) : ℝ :=
  (ArithmeticFunction.sigma k (n + j) : ℝ) / (n.ascFactorial (j + 1) : ℝ)

/-- The generic finite Stirling expansion, in the `n!` indexing convention. -/
noncomputable def genericDilationTailMain5 (k n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (ArithmeticFunction.sigma k (n + (j + 1)) : ℝ) *
      genericDilationPolynomial5 (j + 1) (k + 1) ((n + (j + 1) : ℕ) : ℝ)

/-- The exact error between the actual generic tail and its finite expansion. -/
noncomputable def genericDilationTailError5 (k n : ℕ) : ℝ :=
  genericScaledFullTail5 k (n + 1) - genericDilationTailMain5 k n

/-- The omitted actual tail after `H` ascending-factorial terms. -/
noncomputable def genericDilationOmittedTail5 (k n H : ℕ) : ℝ :=
  ∑' r : ℕ, genericBlockTerm5 k (n + 1) (r + H)

theorem genericPrefix5_at_five (n : ℕ) : genericPrefix5 5 n = prefix5 n := rfl

theorem genericScaledFullTail5_at_five (n : ℕ) :
    genericScaledFullTail5 5 n = scaledFullTail5 n := rfl

/-- The factorial-scaled actual prefix is integral for every exponent. -/
theorem genericPrefix5_scaled_integral (k n : ℕ) :
    ∃ z : ℤ, ((n - 1).factorial : ℝ) * genericPrefix5 k n = z := by
  let z : ℕ := ∑ m ∈ Finset.range n,
    ((n - 1).factorial / m.factorial) * ArithmeticFunction.sigma k m
  refine ⟨(z : ℤ), ?_⟩
  unfold genericPrefix5 z
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hm)
  push_cast [Nat.factorial_dvd_factorial hmn]
  field

/-- Rationality makes every sufficiently late actual scaled tail integral. -/
theorem eventually_genericScaledFullTail5_integral (k : ℕ)
    (hx : ¬ Irrational (alpha k)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ z : ℤ, genericScaledFullTail5 k n = z := by
  obtain ⟨N, hN⟩ := eventually_factorial_mul_eq_int_of_not_irrational hx
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨za, hza⟩ := hN (n - 1) (by omega)
  obtain ⟨zp, hzp⟩ := genericPrefix5_scaled_integral k n
  refine ⟨za - zp, ?_⟩
  unfold genericScaledFullTail5
  rw [mul_sub, hza, hzp]
  exact (Int.cast_sub za zp).symm

private theorem generic_factorial_ratio5 (n j : ℕ) (hn : 0 < n) :
    ((n - 1).factorial : ℝ) / ((n + j).factorial : ℝ) =
      1 / (n.ascFactorial (j + 1) : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have ha : ((m + 1).ascFactorial (j + 1) : ℝ) ≠ 0 := by positivity
  field_simp
  norm_cast
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.add_assoc, Nat.add_comm 1] using
    Nat.factorial_mul_ascFactorial m (j + 1)

private theorem generic_scaled_summand_eq_block5 (k n j : ℕ) (hn : 0 < n) :
    ((n - 1).factorial : ℝ) *
        ((ArithmeticFunction.sigma k (j + n) : ℝ) / ((j + n).factorial : ℝ)) =
      genericBlockTerm5 k n j := by
  rw [Nat.add_comm j n]
  unfold genericBlockTerm5
  rw [mul_div_left_comm, generic_factorial_ratio5 n j hn, mul_one_div]

theorem genericScaledFullTail5_eq_tsum_block (k n : ℕ) (hn : 0 < n) :
    genericScaledFullTail5 k n = ∑' j : ℕ, genericBlockTerm5 k n j := by
  unfold genericScaledFullTail5 alpha genericPrefix5
  rw [← (Tail.summable_sigma_div_factorial k).sum_add_tsum_nat_add n,
    add_sub_cancel_left, ← tsum_mul_left]
  exact tsum_congr (fun j => generic_scaled_summand_eq_block5 k n j hn)

theorem summable_genericBlockTerm5 (k n : ℕ) (hn : 0 < n) :
    Summable (genericBlockTerm5 k n) := by
  exact (((summable_nat_add_iff n).2 (Tail.summable_sigma_div_factorial k)).mul_left
    ((n - 1).factorial : ℝ)).congr
    (fun j => generic_scaled_summand_eq_block5 k n j hn)

theorem genericBlockTerm5_nonneg (k n j : ℕ) : 0 ≤ genericBlockTerm5 k n j := by
  unfold genericBlockTerm5
  positivity

theorem genericDilationOmittedTail5_nonneg (k n H : ℕ) :
    0 ≤ genericDilationOmittedTail5 k n H :=
  tsum_nonneg (fun r => genericBlockTerm5_nonneg k (n + 1) (r + H))

/-- Splitting the actual tail at any finite order. -/
theorem genericScaledFullTail5_split (k n H : ℕ) :
    genericScaledFullTail5 k (n + 1) =
      (∑ j ∈ Finset.range H, genericBlockTerm5 k (n + 1) j) +
        genericDilationOmittedTail5 k n H := by
  rw [genericScaledFullTail5_eq_tsum_block k (n + 1) (by omega)]
  exact ((summable_genericBlockTerm5 k (n + 1) (by omega)).sum_add_tsum_nat_add H).symm

/-- Each actual block summand has exactly the generic denominator error. -/
theorem genericBlockTerm5_expansion (k n j L : ℕ) :
    genericBlockTerm5 k (n + 1) j =
      (ArithmeticFunction.sigma k (n + (j + 1)) : ℝ) *
        genericDilationPolynomial5 (j + 1) L ((n + (j + 1) : ℕ) : ℝ) +
      (ArithmeticFunction.sigma k (n + (j + 1)) : ℝ) *
        genericDilationError5 (j + 1) L ((n + (j + 1) : ℕ) : ℝ) := by
  unfold genericBlockTerm5 genericDilationError5
  rw [genericDilationReciprocal5_centered, Nat.add_right_comm n 1 j]
  ring_nf

/-- Exact decomposition of the generic actual expansion error into the
omitted infinite tail and the finite denominator remainders. -/
theorem genericDilationTailError5_eq (k n : ℕ) :
    genericDilationTailError5 k n = genericDilationOmittedTail5 k n (k + 1) +
      ∑ j ∈ Finset.range (k + 1),
        (ArithmeticFunction.sigma k (n + (j + 1)) : ℝ) *
          genericDilationError5 (j + 1) (k + 1) ((n + (j + 1) : ℕ) : ℝ) := by
  unfold genericDilationTailError5 genericDilationTailMain5
  rw [genericScaledFullTail5_split k n (k + 1)]
  simp_rw [genericBlockTerm5_expansion k n _ (k + 1)]
  rw [Finset.sum_add_distrib]
  ring

theorem genericDilationTail5_expansion (k n : ℕ) :
    genericScaledFullTail5 k (n + 1) =
      genericDilationTailMain5 k n + genericDilationTailError5 k n := by
  unfold genericDilationTailError5
  ring

theorem genericDilationTailError5_nonneg (k n : ℕ) (hn : k + 1 ≤ n) :
    0 ≤ genericDilationTailError5 k n := by
  rw [genericDilationTailError5_eq]
  refine add_nonneg (genericDilationOmittedTail5_nonneg k n (k + 1))
    (Finset.sum_nonneg (fun j hj => mul_nonneg (Nat.cast_nonneg _) ?_))
  exact (genericDilationError5_bounds (k + 1) (k + 1) ((n + (j + 1) : ℕ) : ℝ)
    (by exact_mod_cast (show k + 1 ≤ n + (j + 1) by omega)) (j + 1)
    (by omega) (by have := Finset.mem_range.mp hj; omega)).1

theorem genericDilation_sum_range_succ_eq_Icc (L : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range L, f (j + 1)) = ∑ h ∈ Finset.Icc 1 L, f h := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]

theorem genericDilationPolynomial5_eq_Icc (h L : ℕ) (x : ℝ) :
    genericDilationPolynomial5 h L x =
      ∑ ell ∈ Finset.Icc 1 L,
        (Nat.stirlingSecond (ell - 1) (h - 1) : ℝ) / x ^ ell := by
  simpa only [genericDilationPolynomial5, Nat.add_sub_cancel] using
    genericDilation_sum_range_succ_eq_Icc L
      (fun ell => (Nat.stirlingSecond (ell - 1) (h - 1) : ℝ) / x ^ ell)

/-- The actual finite main term in the common `Icc` convention for both indices. -/
theorem genericDilationTailMain5_eq_Icc (k n : ℕ) :
    genericDilationTailMain5 k n =
      ∑ h ∈ Finset.Icc 1 (k + 1), ∑ ell ∈ Finset.Icc 1 (k + 1),
        (Nat.stirlingSecond (ell - 1) (h - 1) : ℝ) *
          (ArithmeticFunction.sigma k (n + h) : ℝ) / ((n + h : ℕ) : ℝ) ^ ell := by
  unfold genericDilationTailMain5
  rw [genericDilation_sum_range_succ_eq_Icc (k + 1) (fun h =>
    (ArithmeticFunction.sigma k (n + h) : ℝ) *
      genericDilationPolynomial5 h (k + 1) ((n + h : ℕ) : ℝ))]
  simp_rw [genericDilationPolynomial5_eq_Icc, Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_comm, mul_assoc]

#print axioms genericPrefix5_at_five
#print axioms genericScaledFullTail5_at_five
#print axioms genericPrefix5_scaled_integral
#print axioms eventually_genericScaledFullTail5_integral
#print axioms generic_factorial_ratio5
#print axioms generic_scaled_summand_eq_block5
#print axioms genericScaledFullTail5_eq_tsum_block
#print axioms summable_genericBlockTerm5
#print axioms genericBlockTerm5_nonneg
#print axioms genericDilationOmittedTail5_nonneg
#print axioms genericScaledFullTail5_split
#print axioms genericBlockTerm5_expansion
#print axioms genericDilationTailError5_eq
#print axioms genericDilationTail5_expansion
#print axioms genericDilationTailError5_nonneg
#print axioms genericDilation_sum_range_succ_eq_Icc
#print axioms genericDilationPolynomial5_eq_Icc
#print axioms genericDilationTailMain5_eq_Icc

end Erdos252
