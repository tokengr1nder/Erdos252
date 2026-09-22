import Generalizations.Examples

/-!
# Simultaneous numerator and denominator generalisation

Both `a : ℕ → ℤ` and `q : ℕ → ℕ` are arbitrary functions. A telescoping
integer correction may be removed before applying the small-coefficient
criterion. This includes numerators whose ratio to the current base does
not tend to zero. Summability of the normalized correction is explicit:
ordinary conditional convergence must not be confused with Lean's `tsum`.
-/

namespace Erdos252.Generalizations

open Filter
open scoped BigOperators Topology ArithmeticFunction.sigma

noncomputable section

/-- The part of a numerator left after removing a telescoping correction. -/
def residual (a b : ℕ → ℤ) (q : ℕ → ℕ) (n : ℕ) : ℤ :=
  a n - (q n : ℤ) * b n + b (n + 1)

theorem reciprocal_denom_bound {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n) (n : ℕ) :
    1 / (denom q n : ℝ) ≤ (1 / 2 : ℝ) ^ n := by
  rw [div_pow, one_pow]
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast (by simpa using denom_growth hq 0 n : 2 ^ n ≤ denom q n)

/-- Bounded integer correction sequences always meet the summability condition. -/
theorem summable_bounded_correction {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n)
    (b : ℕ → ℤ) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ n, ‖(b n : ℝ)‖ ≤ B) :
    Summable (fun n => (b n : ℝ) / denom q n) := by
  refine ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left B).of_norm_bounded fun n => ?_
  rw [norm_div, Real.norm_natCast]
  calc
    _ ≤ B / denom q n := div_le_div_of_nonneg_right (hb n) (Nat.cast_nonneg _)
    _ ≤ _ := by simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left (reciprocal_denom_bound hq n) hB

theorem normalized_term_eq {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n)
    (a b : ℕ → ℤ) (n : ℕ) :
    cantorTerm a q n = (b n : ℝ) / denom q n -
      (b (n + 1) : ℝ) / denom q (n + 1) + cantorTerm (residual a b q) q n := by
  have hD : (denom q n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (denom_pos hq n).ne'
  have hq0 : (q n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hq n; omega)
  simp only [cantorTerm, residual, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, denom_succ, Nat.cast_mul]
  field_simp
  ring

/-- Exact summation of the telescoping part, with convergence proved. -/
theorem hasSum_normalized {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n) (a b : ℕ → ℤ)
    (hb : Summable (fun n => (b n : ℝ) / denom q n))
    (hr : Summable (cantorTerm (residual a b q) q)) :
    HasSum (cantorTerm a q) ((b 0 : ℝ) + cantorSum (residual a b q) q) := by
  have hb1 := (summable_nat_add_iff 1).mpr hb
  have heq : (∑' n, (b n : ℝ) / denom q n) -
      (∑' n, (b (n + 1) : ℝ) / denom q (n + 1)) = (b 0 : ℝ) := by
    rw [← hb.sum_add_tsum_nat_add 1]
    simp
  have ht := hb.hasSum.sub hb1.hasSum
  rw [heq] at ht
  exact (ht.add hr.hasSum).congr_fun (normalized_term_eq hq a b)

/-- Both functions are free. After an explicitly summable integer correction,
the residual/base ratio must tend to zero and the residual must not vanish
eventually. Neither a divisor sum nor a factorial occurs in this statement. -/
theorem irrational_joint_product_series {a b : ℕ → ℤ} {q : ℕ → ℕ}
    (hq : ∀ n, 2 ≤ q n)
    (hb : Summable (fun n => (b n : ℝ) / denom q n))
    (hr : Tendsto (fun n => (residual a b q n : ℝ) / q n) atTop (𝓝 0))
    (hne : ¬ ∀ᶠ n in atTop, residual a b q n = 0) :
    Irrational (∑' n : ℕ, (a n : ℝ) / (∏ j ∈ Finset.range (n + 1), q j : ℕ)) := by
  have hs := hasSum_normalized hq a b hb (summable_cantor hq hr)
  change Irrational (∑' n, cantorTerm a q n)
  rw [hs.tsum_eq]
  exact (irrational_cantor hq hr hne).intCast_add (b 0)

/-- Under the displayed analytic hypotheses, this is a complete classification,
not merely a sufficient condition. -/
theorem irrational_joint_product_series_iff {a b : ℕ → ℤ} {q : ℕ → ℕ}
    (hq : ∀ n, 2 ≤ q n)
    (hb : Summable (fun n => (b n : ℝ) / denom q n))
    (hr : Tendsto (fun n => (residual a b q n : ℝ) / q n) atTop (𝓝 0)) :
    Irrational (∑' n : ℕ, (a n : ℝ) / (∏ j ∈ Finset.range (n + 1), q j : ℕ)) ↔
      ¬ ∀ᶠ n in atTop, residual a b q n = 0 := by
  change Irrational (∑' n, cantorTerm a q n) ↔ _
  rw [(hasSum_normalized hq a b hb (summable_cantor hq hr)).tsum_eq,
    irrational_intCast_add_iff]
  exact irrational_cantor_iff hq hr

/-- A sharp warning against an unrestricted claim: these positive numerator
and denominator functions give exactly the rational value one. -/
theorem telescoping_counterexample {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n) :
    (∑' n : ℕ, ((q n : ℝ) - 1) / denom q (n + 1)) = 1 := by
  have hb := summable_bounded_correction hq (fun _ => (1 : ℤ)) 1
    (by norm_num) (by intro n; norm_num)
  have hr : residual (fun n => (q n : ℤ) - 1) (fun _ => 1) q = 0 := by
    funext n
    simp [residual]
  have hs := hasSum_normalized hq (fun n => (q n : ℤ) - 1) (fun _ => 1) hb
    (by
      rw [hr]
      unfold cantorTerm
      simp)
  simpa [cantorTerm, cantorSum, hr] using hs.tsum_eq

/-- A simultaneous family with arbitrary bounded integer corrections and
arbitrary sufficiently large integer bases, including nonmonotone bases. -/
theorem irrational_corrected_sigma_product (k : ℕ) (q : ℕ → ℕ)
    (hq : ∀ n, (n + 2) ^ (k + 1) ≤ q n) (b : ℕ → ℤ)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ n, ‖(b n : ℝ)‖ ≤ B) :
    Irrational (∑' n : ℕ,
      ((σ k (n + 2) : ℝ) + (q n : ℝ) * (b n : ℝ) - (b (n + 1) : ℝ)) /
        (∏ j ∈ Finset.range (n + 1), q j : ℕ)) := by
  let a : ℕ → ℤ := fun n => (σ k (n + 2) : ℤ) + (q n : ℤ) * b n - b (n + 1)
  have hr : residual a b q = fun n => (σ k (n + 2) : ℤ) := by
    funext n
    dsimp [residual, a]
    ring
  have hsigma : Summable (cantorTerm (fun n => (σ k (n + 2) : ℤ)) q) := by
    apply summable_cantor (bases_ge_two hq)
    apply squeeze_zero_norm (a := fun n => (σ k (n + 2) : ℝ) /
      ((n + 2 : ℕ) : ℝ) ^ (k + 1))
    · intro n
      simp only [Int.cast_natCast, norm_div, Real.norm_natCast]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        (by exact_mod_cast hq n)
    · exact tendsto_sigma_ratio k
  have hs := hasSum_normalized (bases_ge_two hq) a b
    (summable_bounded_correction (bases_ge_two hq) b B hB hb) (by rw [hr]; exact hsigma)
  have hirr := (irrational_sigma_product k q hq).intCast_add (b 0)
  rw [← hr] at hsigma
  change Irrational ((b 0 : ℝ) + cantorSum (fun n => (σ k (n + 2) : ℤ)) q) at hirr
  rw [← hr, ← hs.tsum_eq] at hirr
  simpa only [cantorTerm, a, Int.cast_sub, Int.cast_add, Int.cast_mul,
    Int.cast_natCast, denom] using hirr

end

end Erdos252.Generalizations
