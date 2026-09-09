import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Generic finite reciprocal-denominator expansion

For `1 ≤ h ≤ H ≤ x`, the reciprocal descending product has its Stirling
expansion through any order `L`, with nonnegative error at most
`H^L / x^(L+1)`. This is finite real algebra, not an assertion about the
value of any factorial series.
-/

namespace Erdos252

open scoped BigOperators

/-- The reciprocal product centered at its largest factor. -/
noncomputable def genericDilationReciprocal5 (h : ℕ) (x : ℝ) : ℝ :=
  1 / ∏ j ∈ Finset.range h, (x - (j : ℝ))

/-- The Stirling expansion through reciprocal degree `L`. -/
noncomputable def genericDilationPolynomial5 (h L : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range L, (Nat.stirlingSecond i (h - 1) : ℝ) / x ^ (i + 1)

/-- The exact remainder after the finite Stirling expansion. -/
noncomputable def genericDilationError5 (h L : ℕ) (x : ℝ) : ℝ :=
  genericDilationReciprocal5 h x - genericDilationPolynomial5 h L x

theorem genericDilationReciprocal5_succ (h : ℕ) (x : ℝ) :
    genericDilationReciprocal5 (h + 1) x =
      genericDilationReciprocal5 h x / (x - (h : ℝ)) := by
  simp only [genericDilationReciprocal5, Finset.prod_range_succ, div_div]

theorem genericDilationReciprocal5_one (x : ℝ) :
    genericDilationReciprocal5 1 x = 1 / x := by
  simp [genericDilationReciprocal5]

/-- The centered product satisfies the same linear recurrence as its coefficients. -/
theorem genericDilationReciprocal5_recurrence (h : ℕ) (x : ℝ)
    (hh : x - (h : ℝ) ≠ 0) :
    x * genericDilationReciprocal5 (h + 1) x =
      genericDilationReciprocal5 h x +
        (h : ℝ) * genericDilationReciprocal5 (h + 1) x := by
  rw [genericDilationReciprocal5_succ]
  field_simp
  ring

theorem genericDilationPolynomial5_zero (h : ℕ) (x : ℝ) :
    genericDilationPolynomial5 h 0 x = 0 := by
  simp [genericDilationPolynomial5]

theorem genericDilationPolynomial5_one (L : ℕ) (x : ℝ) :
    genericDilationPolynomial5 1 (L + 1) x = 1 / x := by
  simp [genericDilationPolynomial5, Finset.sum_range_succ', Nat.stirlingSecond]

/-- The finite coefficient recurrence holds at every truncation order. -/
theorem genericDilationPolynomial5_recurrence (h L : ℕ) (x : ℝ) (hh : 1 ≤ h) :
    genericDilationPolynomial5 (h + 1) (L + 1) x =
      (genericDilationPolynomial5 h L x +
        (h : ℝ) * genericDilationPolynomial5 (h + 1) L x) / x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  unfold genericDilationPolynomial5
  rw [Finset.sum_range_succ']
  simp only [Nat.succ_sub_one, Nat.stirlingSecond_zero_succ,
    Nat.cast_zero, zero_div, add_zero]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.stirlingSecond_succ_succ]
  push_cast
  simp only [pow_succ, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Consequently the exact errors obey a positive finite recurrence. -/
theorem genericDilationError5_recurrence (h L : ℕ) (x : ℝ)
    (hh : 1 ≤ h) (hx : x ≠ 0) (hxh : x - (h : ℝ) ≠ 0) :
    genericDilationError5 (h + 1) (L + 1) x =
      (genericDilationError5 h L x +
        (h : ℝ) * genericDilationError5 (h + 1) L x) / x := by
  have hr := genericDilationReciprocal5_recurrence h x hxh
  unfold genericDilationError5
  rw [genericDilationPolynomial5_recurrence h L x hh]
  apply (eq_div_iff hx).mpr
  field_simp
  nlinarith

/-- A centered descending product is positive and its reciprocal is at most
`1/x` once all its factors other than `x` are at least one. -/
theorem genericDilationReciprocal5_bounds (h H : ℕ) (x : ℝ)
    (hh : 1 ≤ h) (hH : h ≤ H) (hx : (H : ℝ) ≤ x) :
    0 < genericDilationReciprocal5 h x ∧ genericDilationReciprocal5 h x ≤ 1 / x := by
  induction h, hh using Nat.le_induction with
  | base =>
    rw [genericDilationReciprocal5_one]
    exact ⟨one_div_pos.mpr (lt_of_lt_of_le one_pos ((Nat.one_le_cast.mpr hH).trans hx)),
      le_rfl⟩
  | succ h hh ih =>
    have hdiff : (1 : ℝ) ≤ x - h := by
      have := (Nat.cast_le (α := ℝ)).mpr hH
      push_cast at this
      linarith
    have hb := ih (by omega)
    rw [genericDilationReciprocal5_succ]
    exact ⟨div_pos hb.1 (by linarith), (div_le_self hb.1.le hdiff).trans hb.2⟩

/-- The finite error bound is uniform over all product lengths `1..H`.
No convergence theorem or unproved asymptotic hypothesis is used. -/
theorem genericDilationError5_bounds (H L : ℕ) (x : ℝ) (hx : (H : ℝ) ≤ x)
    (h : ℕ) (hh : 1 ≤ h) (hH : h ≤ H) :
    0 ≤ genericDilationError5 h L x ∧
      genericDilationError5 h L x ≤ (H : ℝ) ^ L / x ^ (L + 1) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by exact_mod_cast (show 0 < H by omega)) hx
  induction L generalizing h with
  | zero =>
    simp only [genericDilationError5, genericDilationPolynomial5_zero, sub_zero,
      pow_zero, zero_add, pow_one]
    exact ⟨(genericDilationReciprocal5_bounds h H x hh hH hx).1.le,
      (genericDilationReciprocal5_bounds h H x hh hH hx).2⟩
  | succ L ih =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [genericDilationError5, genericDilationReciprocal5_one,
        genericDilationPolynomial5_one, sub_self]
      exact ⟨le_rfl, by positivity⟩
    have hdiff : 0 < x - (j : ℝ) := by
      have hjR : (j : ℝ) + 1 ≤ H := by exact_mod_cast hH
      linarith
    have hprev := ih j hj (by omega)
    have hcurr := ih (j + 1) hh hH
    rw [genericDilationError5_recurrence j L x hj hxpos.ne' hdiff.ne']
    refine ⟨div_nonneg (add_nonneg hprev.1 (mul_nonneg (Nat.cast_nonneg j) hcurr.1))
      hxpos.le, ?_⟩
    calc
      _ ≤ ((H : ℝ) ^ L / x ^ (L + 1) +
          (j : ℝ) * ((H : ℝ) ^ L / x ^ (L + 1))) / x :=
        (div_le_div_iff_of_pos_right hxpos).mpr
          (add_le_add hprev.2 (mul_le_mul_of_nonneg_left hcurr.2 (Nat.cast_nonneg j)))
      _ = ((j : ℝ) + 1) * (H : ℝ) ^ L / x ^ (L + 2) := by
        rw [pow_succ x (L + 1)]
        ring
      _ ≤ (H : ℝ) * (H : ℝ) ^ L / x ^ (L + 2) := by
        gcongr
        exact_mod_cast hH
      _ = (H : ℝ) ^ (L + 1) / x ^ (L + 1 + 1) := by ring

private theorem genericDilation_ascFactorial_cast (n h : ℕ) :
    ((n + 1).ascFactorial h : ℝ) =
      ∏ j ∈ Finset.range h, ((n : ℝ) + 1 + (j : ℝ)) := by
  simp only [Nat.ascFactorial_eq_prod_range, Nat.cast_prod, Nat.cast_add, Nat.cast_one]

/-- The generic descending product is exactly the actual ascending-factorial
denominator when centered at its largest factor. -/
theorem genericDilationReciprocal5_centered (n h : ℕ) :
    genericDilationReciprocal5 h ((n + h : ℕ) : ℝ) =
      1 / ((n + 1).ascFactorial h : ℝ) := by
  unfold genericDilationReciprocal5
  rw [genericDilation_ascFactorial_cast]
  congr 1
  rw [← Finset.prod_range_reflect (fun j : ℕ => ((n + h : ℕ) : ℝ) - (j : ℝ)) h]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hjh := Finset.mem_range.mp hj
  push_cast [Nat.cast_sub (by omega : j ≤ h - 1), Nat.cast_sub (by omega : 1 ≤ h)]
  ring

#print axioms genericDilationReciprocal5_succ
#print axioms genericDilationReciprocal5_one
#print axioms genericDilationReciprocal5_recurrence
#print axioms genericDilationPolynomial5_zero
#print axioms genericDilationPolynomial5_one
#print axioms genericDilationPolynomial5_recurrence
#print axioms genericDilationError5_recurrence
#print axioms genericDilationReciprocal5_bounds
#print axioms genericDilationError5_bounds
#print axioms genericDilationReciprocal5_centered

end Erdos252
