import Erdos252.AffineCongruenceCount
import Erdos252.ProgressionMeanSupport
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Actual divisor-phase means in every positive degree

The real phase `sigma k n / n^k` is a finite sum of periodic
reciprocal-divisor terms. Positive affine arguments inject their divisible
values into positive multiples, which gives an averaged bound with denominator
exponent `k+1`. Dominated convergence then yields the arithmetic-progression
mean as the explicit local gcd series, in every positive degree including the
non-uniformly bounded degree one.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

noncomputable section

def rawPhase (k n : ℕ) : ℝ := (ArithmeticFunction.sigma k n : ℝ) / (n : ℝ) ^ k

def rawPhaseDivisorTerm (k d n : ℕ) : ℝ :=
  if d ∣ n then 1 / (d : ℝ) ^ k else 0

def rawPhaseProgressionMeanTerm (k Q A d : ℕ) : ℝ :=
  (∑ j ∈ Finset.range d, rawPhaseDivisorTerm k d (Q * j + A)) / (d : ℝ)

def rawPhaseProgressionMean (k Q A : ℕ) : ℝ :=
  ∑' d : ℕ, rawPhaseProgressionMeanTerm k Q A d

theorem rawPhaseDivisorTerm_bounds (k d n : ℕ) :
    0 ≤ rawPhaseDivisorTerm k d n ∧ rawPhaseDivisorTerm k d n ≤ 1 / (d : ℝ) ^ k := by
  unfold rawPhaseDivisorTerm
  split_ifs <;> constructor <;> first | exact le_rfl | positivity

/-- The phase is the finite sum of its reciprocal divisor powers. -/
theorem hasSum_rawPhaseDivisorTerm (k : ℕ) {n : ℕ} (hn : 0 < n) :
    HasSum (fun d => rawPhaseDivisorTerm k d n) (rawPhase k n) := by
  have hsum : rawPhase k n = ∑ d ∈ n.divisors, rawPhaseDivisorTerm k d n := by
    unfold rawPhase
    rw [ArithmeticFunction.sigma_eq_sum_div]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [rawPhaseDivisorTerm, if_pos (Nat.dvd_of_mem_divisors hd),
      Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd), div_pow, div_right_comm,
      div_self (by positivity : (n : ℝ) ^ k ≠ 0)]
  rw [hsum]
  refine hasSum_sum_of_ne_finset_zero fun d hd => ?_
  simp only [Nat.mem_divisors, hn.ne', ne_eq, not_false_eq_true, and_true] at hd
  simp [rawPhaseDivisorTerm, hd]

theorem rawPhaseDivisorTerm_cesaro {k : ℕ} (hk : 0 < k) (Q A d : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, rawPhaseDivisorTerm k d (Q * n + A)) / (N : ℝ)) atTop
      (𝓝 (rawPhaseProgressionMeanTerm k Q A d)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [rawPhaseDivisorTerm, rawPhaseProgressionMeanTerm, zero_pow hk.ne']
  · refine periodic_nonneg_cesaro5 hd (fun n => ?_)
      (fun n => (rawPhaseDivisorTerm_bounds k d _).1)
    simp only [rawPhaseDivisorTerm, Nat.mul_add, Nat.add_right_comm (Q * n),
      ← Nat.dvd_add_iff_left (dvd_mul_left d Q)]

theorem rawPhaseProgressionMeanTerm_eq_gcd (k Q A d : ℕ) :
    rawPhaseProgressionMeanTerm k Q A d =
      if Nat.gcd d Q ∣ A then (Nat.gcd d Q : ℝ) / (d : ℝ) ^ (k + 1) else 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [rawPhaseProgressionMeanTerm]
  · unfold rawPhaseProgressionMeanTerm rawPhaseDivisorTerm
    rw [← Finset.sum_filter, Finset.sum_const, affineCongruence5_count_period Q A d hd]
    split_ifs
    · simp only [nsmul_eq_mul, pow_succ]
      ring
    · simp

/-- Positive affine values that are divisible by `d` inject into the multiples
of `d` up to the largest value. -/
theorem affineCongruence_count_le_quotient {Q A d : ℕ}
    (hQ : 0 < Q) (hA : 0 < A) (N : ℕ) :
    ((Finset.range N).filter (fun n => d ∣ Q * n + A)).card ≤ (Q * N + A) / d := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  refine Finset.card_le_card_of_injOn (fun n => Q * n + A) (fun n hn => ?_)
    (fun n _ m _ h => Nat.eq_of_mul_eq_mul_left hQ (Nat.add_right_cancel h))
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hn ⊢
  exact ⟨⟨by omega, Nat.add_le_add_right (Nat.mul_le_mul_left Q hn.1.le) A⟩, hn.2⟩

theorem rawPhaseDivisorTerm_cesaro_bound {k Q A : ℕ}
    (hk : 0 < k) (hQ : 0 < Q) (hA : 0 < A) (d N : ℕ) :
    ‖(∑ n ∈ Finset.range N, rawPhaseDivisorTerm k d (Q * n + A)) / (N : ℝ)‖ ≤
      ((Q + A : ℕ) : ℝ) / (d : ℝ) ^ (k + 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, div_zero, norm_zero]
    positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [rawPhaseDivisorTerm, zero_pow hk.ne']
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmul : (((Finset.range N).filter (fun n => d ∣ Q * n + A)).card : ℝ) * d ≤
      ((Q + A : ℕ) : ℝ) * N := by
    have hcard := affineCongruence_count_le_quotient hQ hA N (d := d)
    exact_mod_cast (Nat.mul_le_mul_right d hcard).trans
      ((Nat.div_mul_le_self _ _).trans (by nlinarith))
  have heq : (∑ n ∈ Finset.range N, rawPhaseDivisorTerm k d (Q * n + A)) / (N : ℝ) =
      (((Finset.range N).filter (fun n => d ∣ Q * n + A)).card : ℝ) / ((d : ℝ) ^ k * N) := by
    unfold rawPhaseDivisorTerm
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [heq, Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_succ,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hmul (pow_nonneg hdR.le k)]

theorem rawPhaseProgressionMeanTerm_bounds {k Q : ℕ} (hQ : 0 < Q) (A d : ℕ) :
    0 ≤ rawPhaseProgressionMeanTerm k Q A d ∧
      rawPhaseProgressionMeanTerm k Q A d ≤ (Q : ℝ) / (d : ℝ) ^ (k + 1) := by
  rw [rawPhaseProgressionMeanTerm_eq_gcd]
  split_ifs <;> refine ⟨by positivity, ?_⟩
  · exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.gcd_le_right d hQ)
      (by positivity)
  · positivity

theorem summable_rawPhaseProgressionMeanTerm {k Q : ℕ} (hk : 0 < k) (hQ : 0 < Q) (A : ℕ) :
    Summable (rawPhaseProgressionMeanTerm k Q A) :=
  Summable.of_nonneg_of_le (fun d => (rawPhaseProgressionMeanTerm_bounds hQ A d).1)
    (fun d => (rawPhaseProgressionMeanTerm_bounds hQ A d).2)
    (by simpa only [mul_one_div] using
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k + 1)).mul_left (Q : ℝ))

theorem one_le_rawPhaseProgressionMean {k Q : ℕ} (hk : 0 < k) (hQ : 0 < Q) (A : ℕ) :
    1 ≤ rawPhaseProgressionMean k Q A := by
  have hh := (summable_rawPhaseProgressionMeanTerm hk hQ A).le_tsum 1
    (fun d _ => (rawPhaseProgressionMeanTerm_bounds hQ A d).1)
  simpa [rawPhaseProgressionMean, rawPhaseProgressionMeanTerm, rawPhaseDivisorTerm] using hh

/-- The actual phase averages along any positive arithmetic progression. -/
theorem rawPhase_cesaro_progression {k Q A : ℕ} (hk : 0 < k) (hQ : 0 < Q) (hA : 0 < A) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, rawPhase k (Q * n + A)) / (N : ℝ)) atTop
      (𝓝 (rawPhaseProgressionMean k Q A)) := by
  have hs : Summable (fun d : ℕ => ((Q + A : ℕ) : ℝ) / (d : ℝ) ^ (k + 1)) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k + 1)).mul_left ((Q + A : ℕ) : ℝ)
  refine (tendsto_tsum_of_dominated_convergence hs (fun d => rawPhaseDivisorTerm_cesaro hk Q A d)
    (Eventually.of_forall (fun N d => rawPhaseDivisorTerm_cesaro_bound hk hQ hA d N))).congr'
    (Eventually.of_forall fun N => ?_)
  rw [tsum_div_const,
    (hasSum_sum fun n _ => hasSum_rawPhaseDivisorTerm k (by omega : 0 < Q * n + A)).tsum_eq]

#print axioms rawPhaseDivisorTerm_bounds
#print axioms hasSum_rawPhaseDivisorTerm
#print axioms rawPhaseDivisorTerm_cesaro
#print axioms rawPhaseProgressionMeanTerm_eq_gcd
#print axioms affineCongruence_count_le_quotient
#print axioms rawPhaseDivisorTerm_cesaro_bound
#print axioms rawPhaseProgressionMeanTerm_bounds
#print axioms summable_rawPhaseProgressionMeanTerm
#print axioms one_le_rawPhaseProgressionMean
#print axioms rawPhase_cesaro_progression

end

end Erdos252
