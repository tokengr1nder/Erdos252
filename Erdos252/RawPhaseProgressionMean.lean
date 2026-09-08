import Erdos252.AffineCongruenceCount
import Erdos252.ProgressionMeanSupport
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Actual divisor-phase means in every degree at least two

The real phase `sigma k n / n^k` is an absolutely and uniformly convergent
series of periodic reciprocal-divisor terms. Its arithmetic-progression mean
is the explicit local gcd series with denominator exponent `k+1`.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

noncomputable section

def rawPhase (k n : ℕ) : ℝ := (ArithmeticFunction.sigma k n : ℝ) / (n : ℝ) ^ k

def rawPhaseDivisorTerm (k d n : ℕ) : ℝ :=
  if d ∣ n then 1 / (d : ℝ) ^ k else 0

def rawPhaseTruncation (k D n : ℕ) : ℝ :=
  ∑ d ∈ Finset.range D, rawPhaseDivisorTerm k d n

def rawPhaseProgressionMeanTerm (k Q A d : ℕ) : ℝ :=
  (∑ j ∈ Finset.range d, rawPhaseDivisorTerm k d (Q * j + A)) / (d : ℝ)

def rawPhaseProgressionMean (k Q A : ℕ) : ℝ :=
  ∑' d : ℕ, rawPhaseProgressionMeanTerm k Q A d

theorem divisor_quotient_power_ratio (k : ℕ)
    {m d : ℕ} (hm : 0 < m) (hd : d ∈ m.divisors) :
    (((m / d : ℕ) : ℝ) ^ k) / (m : ℝ) ^ k = (1 : ℝ) / (d : ℝ) ^ k := by
  have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hm
  have hquotpos : 0 < m / d := Nat.div_pos (Nat.le_of_dvd hm hdvd) hdpos
  have hfactor : ((m / d : ℕ) : ℝ) * d = m := by
    exact_mod_cast Nat.div_mul_cancel hdvd
  rw [← hfactor]
  field_simp
  exact (mul_pow _ _ _).symm

theorem rawPhase_eq_sum_divisors_reciprocal (k : ℕ) {n : ℕ} (hn : 0 < n) :
    rawPhase k n = ∑ d ∈ n.divisors, (1 : ℝ) / (d : ℝ) ^ k := by
  unfold rawPhase
  rw [ArithmeticFunction.sigma_eq_sum_div]
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun d hd => divisor_quotient_power_ratio k hn hd)

theorem rawPhaseDivisorTerm_bounds (k d n : ℕ) :
    0 ≤ rawPhaseDivisorTerm k d n ∧ rawPhaseDivisorTerm k d n ≤ 1 / (d : ℝ) ^ k := by
  unfold rawPhaseDivisorTerm
  split_ifs <;> constructor <;> first | exact le_rfl | positivity

theorem summable_rawPhaseDivisorTerm {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    Summable (fun d => rawPhaseDivisorTerm k d n) := by
  exact Summable.of_nonneg_of_le (fun d => (rawPhaseDivisorTerm_bounds k d n).1)
    (fun d => (rawPhaseDivisorTerm_bounds k d n).2)
    (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k))

theorem rawPhase_eq_tsum_divisorTerm (k : ℕ) {n : ℕ} (hn : 0 < n) :
    rawPhase k n = ∑' d : ℕ, rawPhaseDivisorTerm k d n := by
  rw [rawPhase_eq_sum_divisors_reciprocal k hn]
  symm
  calc
    _ = ∑ d ∈ n.divisors, rawPhaseDivisorTerm k d n := by
      apply tsum_eq_sum
      intro d hd
      have hndvd : ¬ d ∣ n := fun h => hd (Nat.mem_divisors.mpr ⟨h, hn.ne'⟩)
      simp only [rawPhaseDivisorTerm, hndvd, ↓reduceIte]
    _ = _ := Finset.sum_congr rfl (fun d hd => by
      simp only [rawPhaseDivisorTerm, Nat.dvd_of_mem_divisors hd, ↓reduceIte])

theorem rawPhase_truncation_bounds {k n : ℕ} (hk : 2 ≤ k) (hn : 0 < n) (D : ℕ) :
    0 ≤ rawPhase k n - rawPhaseTruncation k (D + 1) n ∧
      rawPhase k n - rawPhaseTruncation k (D + 1) n ≤
        ∑' j : ℕ, 1 / ((j + (D + 1) : ℕ) : ℝ) ^ k := by
  have hsum := (summable_rawPhaseDivisorTerm hk n).sum_add_tsum_nat_add (D + 1)
  have heq : rawPhase k n - rawPhaseTruncation k (D + 1) n =
      ∑' j : ℕ, rawPhaseDivisorTerm k (j + (D + 1)) n := by
    rw [rawPhase_eq_tsum_divisorTerm k hn, ← hsum]
    simp only [rawPhaseTruncation, add_sub_cancel_left]
  rw [heq]
  constructor
  · exact tsum_nonneg (fun j => (rawPhaseDivisorTerm_bounds k _ n).1)
  · have hinj : Function.Injective (fun j : ℕ => j + (D + 1)) :=
      fun _ _ h => Nat.add_right_cancel h
    exact ((summable_rawPhaseDivisorTerm hk n).comp_injective hinj).tsum_le_tsum
      (fun j => (rawPhaseDivisorTerm_bounds k _ n).2)
      ((Real.summable_one_div_nat_pow.mpr (by omega : 1 < k)).comp_injective hinj)

theorem rawPhase_uniform_truncation {k : ℕ} (hk : 2 ≤ k) :
    TendstoUniformlyOn (rawPhaseTruncation k) (rawPhase k) atTop (Set.Ioi 0) := by
  have hbound (d n : ℕ) (_hn : n ∈ Set.Ioi 0) :
      ‖rawPhaseDivisorTerm k d n‖ ≤ 1 / (d : ℝ) ^ k := by
    rw [Real.norm_eq_abs, abs_of_nonneg (rawPhaseDivisorTerm_bounds k d n).1]
    exact (rawPhaseDivisorTerm_bounds k d n).2
  have hu := tendstoUniformlyOn_tsum_nat
    (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k)) hbound
  exact hu.congr_right (fun n hn => (rawPhase_eq_tsum_divisorTerm k hn).symm)

theorem rawPhaseDivisorTerm_cesaro_pos {k : ℕ} (hk : 0 < k) (Q A d : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, rawPhaseDivisorTerm k d (Q * n + A)) / (N : ℝ)) atTop
      (𝓝 (rawPhaseProgressionMeanTerm k Q A d)) := by
  by_cases hd : d = 0
  · subst d
    simp [rawPhaseDivisorTerm, rawPhaseProgressionMeanTerm, zero_pow hk.ne']
  · apply periodic_nonneg_cesaro5 (Nat.pos_of_ne_zero hd)
    · intro n
      unfold rawPhaseDivisorTerm
      dsimp only
      have heq : Q * (n + d) + A = Q * n + A + Q * d := by ring
      rw [heq]
      simp only [← Nat.dvd_add_iff_left (dvd_mul_left d Q)]
    · intro n
      exact (rawPhaseDivisorTerm_bounds k d (Q * n + A)).1

theorem rawPhaseDivisorTerm_cesaro {k : ℕ} (hk : 2 ≤ k) (Q A d : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, rawPhaseDivisorTerm k d (Q * n + A)) / (N : ℝ)) atTop
      (𝓝 (rawPhaseProgressionMeanTerm k Q A d)) := by
  exact rawPhaseDivisorTerm_cesaro_pos (by omega) Q A d

theorem rawPhaseDivisorTerm_cesaro_bound (k Q A d N : ℕ) :
    ‖(∑ n ∈ Finset.range N, rawPhaseDivisorTerm k d (Q * n + A)) / (N : ℝ)‖ ≤
      1 / (d : ℝ) ^ k := by
  by_cases hN : N = 0
  · subst N
    simp
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hs0 : 0 ≤ ∑ n ∈ Finset.range N, rawPhaseDivisorTerm k d (Q * n + A) :=
    Finset.sum_nonneg (fun n _ => (rawPhaseDivisorTerm_bounds k d _).1)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hs0 hn.le)]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) / (d : ℝ) ^ k :=
      Finset.sum_le_sum (fun n _ => (rawPhaseDivisorTerm_bounds k d _).2)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem rawPhaseProgressionMeanTerm_eq_card (k Q A d : ℕ) :
    rawPhaseProgressionMeanTerm k Q A d =
      (((Finset.range d).filter (fun j => d ∣ Q * j + A)).card : ℝ) / (d : ℝ) ^ (k + 1) := by
  unfold rawPhaseProgressionMeanTerm rawPhaseDivisorTerm
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, pow_succ]
  ring

theorem rawPhaseProgressionMeanTerm_bounds {k : ℕ} (hk : 2 ≤ k) (Q A d : ℕ) :
    0 ≤ rawPhaseProgressionMeanTerm k Q A d ∧
      rawPhaseProgressionMeanTerm k Q A d ≤ 1 / (d : ℝ) ^ k := by
  have hn : 0 ≤ rawPhaseProgressionMeanTerm k Q A d := by
    unfold rawPhaseProgressionMeanTerm
    exact div_nonneg (Finset.sum_nonneg
      (fun j _ => (rawPhaseDivisorTerm_bounds k d _).1)) (by positivity)
  refine ⟨hn, ?_⟩
  have hh := le_of_tendsto (rawPhaseDivisorTerm_cesaro hk Q A d).norm
    (Eventually.of_forall (rawPhaseDivisorTerm_cesaro_bound k Q A d))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hh

theorem summable_rawPhaseProgressionMeanTerm {k : ℕ} (hk : 2 ≤ k) (Q A : ℕ) :
    Summable (rawPhaseProgressionMeanTerm k Q A) := by
  exact Summable.of_nonneg_of_le (fun d => (rawPhaseProgressionMeanTerm_bounds hk Q A d).1)
    (fun d => (rawPhaseProgressionMeanTerm_bounds hk Q A d).2)
    (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k))

theorem one_le_rawPhaseProgressionMean {k : ℕ} (hk : 2 ≤ k) (Q A : ℕ) :
    1 ≤ rawPhaseProgressionMean k Q A := by
  have hh := (summable_rawPhaseProgressionMeanTerm hk Q A).le_tsum 1
    (fun d _ => (rawPhaseProgressionMeanTerm_bounds hk Q A d).1)
  simpa [rawPhaseProgressionMean, rawPhaseProgressionMeanTerm, rawPhaseDivisorTerm] using hh

theorem rawPhase_cesaro_progression {k : ℕ} (hk : 2 ≤ k) (Q : ℕ) {A : ℕ} (hA : 0 < A) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, rawPhase k (Q * n + A)) / (N : ℝ)) atTop
      (𝓝 (rawPhaseProgressionMean k Q A)) := by
  have hh := tendsto_tsum_of_dominated_convergence
    (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k))
    (fun d => rawPhaseDivisorTerm_cesaro hk Q A d)
    (Eventually.of_forall (fun N d => rawPhaseDivisorTerm_cesaro_bound k Q A d N))
  apply hh.congr'
  apply Eventually.of_forall
  intro N
  dsimp only
  rw [tsum_div_const,
    Summable.tsum_finsetSum (fun n (_hn : n ∈ Finset.range N) =>
      summable_rawPhaseDivisorTerm hk (Q * n + A))]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact (rawPhase_eq_tsum_divisorTerm k (by omega : 0 < Q * n + A)).symm

theorem rawPhaseProgressionMeanTerm_eq_gcd (k Q A d : ℕ) :
    rawPhaseProgressionMeanTerm k Q A d =
      if Nat.gcd d Q ∣ A then (Nat.gcd d Q : ℝ) / (d : ℝ) ^ (k + 1) else 0 := by
  by_cases hd : d = 0
  · subst d
    simp [rawPhaseProgressionMeanTerm]
  · rw [rawPhaseProgressionMeanTerm_eq_card,
      affineCongruence5_count_period Q A d (Nat.pos_of_ne_zero hd)]
    split_ifs <;> simp

theorem rawPhaseProgressionMean_eq_tsum_gcd (k Q A : ℕ) :
    rawPhaseProgressionMean k Q A =
      ∑' d : ℕ, if Nat.gcd d Q ∣ A then (Nat.gcd d Q : ℝ) / (d : ℝ) ^ (k + 1) else 0 := by
  unfold rawPhaseProgressionMean
  exact tsum_congr (rawPhaseProgressionMeanTerm_eq_gcd k Q A)

theorem rawPhase_cesaro_progression_gcd {k : ℕ} (hk : 2 ≤ k) (Q : ℕ) {A : ℕ}
    (hA : 0 < A) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, rawPhase k (Q * n + A)) / (N : ℝ)) atTop
      (𝓝 (∑' d : ℕ, if Nat.gcd d Q ∣ A then
        (Nat.gcd d Q : ℝ) / (d : ℝ) ^ (k + 1) else 0)) := by
  simpa only [rawPhaseProgressionMean_eq_tsum_gcd] using rawPhase_cesaro_progression hk Q hA

#print axioms divisor_quotient_power_ratio
#print axioms rawPhase_eq_sum_divisors_reciprocal
#print axioms rawPhaseDivisorTerm_bounds
#print axioms summable_rawPhaseDivisorTerm
#print axioms rawPhase_eq_tsum_divisorTerm
#print axioms rawPhase_truncation_bounds
#print axioms rawPhase_uniform_truncation
#print axioms rawPhaseDivisorTerm_cesaro_pos
#print axioms rawPhaseDivisorTerm_cesaro
#print axioms rawPhaseDivisorTerm_cesaro_bound
#print axioms rawPhaseProgressionMeanTerm_eq_card
#print axioms rawPhaseProgressionMeanTerm_bounds
#print axioms summable_rawPhaseProgressionMeanTerm
#print axioms one_le_rawPhaseProgressionMean
#print axioms rawPhase_cesaro_progression
#print axioms rawPhaseProgressionMeanTerm_eq_gcd
#print axioms rawPhaseProgressionMean_eq_tsum_gcd
#print axioms rawPhase_cesaro_progression_gcd

end

end Erdos252
