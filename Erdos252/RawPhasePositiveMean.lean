import Erdos252.RawPhaseFreshPrimeMean
import Erdos252.IsolatedShiftResidues
import Erdos252.IsolatedShiftMeanContradiction

/-!
# Progression means also in degree one

Positive affine arguments let their divisible values inject into positive
multiples. The resulting averaged bound has exponent `k+1`, so the mean
exists for every positive degree, including the non-uniformly bounded degree one.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

noncomputable section

theorem affineCongruence_count_le_quotient {Q A d : ℕ}
    (hQ : 0 < Q) (hA : 0 < A) (hd : 0 < d) (N : ℕ) :
    ((Finset.range N).filter (fun n => d ∣ Q * n + A)).card ≤ (Q * N + A) / d := by
  let S := (Finset.range N).filter (fun n => d ∣ Q * n + A)
  have hmap : Set.MapsTo (fun n : ℕ => (Q * n + A) / d) S
      (Finset.Icc 1 ((Q * N + A) / d)) := by
    intro n hn
    have hmem := Finset.mem_filter.mp hn
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd (by omega : 0 < Q * n + A) hmem.2) hd
    · apply Nat.div_le_div_right
      exact Nat.add_le_add_right (Nat.mul_le_mul_left Q
        (Nat.le_of_lt (Finset.mem_range.mp hmem.1))) A
  have hinj : (S : Set ℕ).InjOn (fun n : ℕ => (Q * n + A) / d) := by
    intro n hn j hj heq
    dsimp only at heq
    have hn' := Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
    have hj' := Nat.div_mul_cancel (Finset.mem_filter.mp hj).2
    rw [heq] at hn'
    have hmul : Q * n = Q * j := by omega
    exact Nat.eq_of_mul_eq_mul_left hQ hmul
  have hh := Finset.card_le_card_of_injOn _ hmap hinj
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hh

theorem summable_rawPhaseDivisorTerm_of_pos (k : ℕ) {n : ℕ} (hn : 0 < n) :
    Summable (fun d => rawPhaseDivisorTerm k d n) := by
  apply summable_of_ne_finset_zero (s := n.divisors)
  intro d hd
  have hndvd : ¬ d ∣ n := fun h => hd (Nat.mem_divisors.mpr ⟨h, hn.ne'⟩)
  simp only [rawPhaseDivisorTerm, hndvd, ↓reduceIte]

theorem rawPhaseDivisorTerm_cesaro_bound_pos {k Q A : ℕ}
    (hk : 0 < k) (hQ : 0 < Q) (hA : 0 < A) (d N : ℕ) :
    ‖(∑ n ∈ Finset.range N, rawPhaseDivisorTerm k d (Q * n + A)) / (N : ℝ)‖ ≤
      ((Q + A : ℕ) : ℝ) / (d : ℝ) ^ (k + 1) := by
  by_cases hN : N = 0
  · subst N
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, div_zero, norm_zero]
    positivity
  by_cases hd : d = 0
  · subst d
    simp [rawPhaseDivisorTerm, zero_pow hk.ne']
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  let C := ((Finset.range N).filter (fun n => d ∣ Q * n + A)).card
  have hcard := affineCongruence_count_le_quotient hQ hA (Nat.pos_of_ne_zero hd) N
  have hmul : C * d ≤ (Q + A) * N := by
    have h1 := Nat.mul_le_mul_right d hcard
    have h2 := Nat.div_mul_le_self (Q * N + A) d
    have h3 : A ≤ A * N := by nlinarith [Nat.pos_of_ne_zero hN]
    dsimp [C]
    nlinarith
  have hmulR : (C : ℝ) * d ≤ ((Q + A : ℕ) : ℝ) * N := by exact_mod_cast hmul
  have heq : (∑ n ∈ Finset.range N, rawPhaseDivisorTerm k d (Q * n + A)) /
      (N : ℝ) = (C : ℝ) / ((d : ℝ) ^ k * N) := by
    unfold rawPhaseDivisorTerm
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp [C]
    ring
  rw [heq, Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_succ]
  apply (div_le_div_iff₀ (by positivity : 0 < (d : ℝ) ^ k * N)
    (by positivity : 0 < (d : ℝ) ^ k * d)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hmulR (pow_nonneg hdR.le k)]

theorem rawPhaseProgressionMeanTerm_bounds_pos {k Q : ℕ}
    (hQ : 0 < Q) (A d : ℕ) :
    0 ≤ rawPhaseProgressionMeanTerm k Q A d ∧
      rawPhaseProgressionMeanTerm k Q A d ≤ (Q : ℝ) / (d : ℝ) ^ (k + 1) := by
  rw [rawPhaseProgressionMeanTerm_eq_gcd]
  split_ifs
  · constructor
    · positivity
    · apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.gcd_le_right d hQ
  · constructor
    · exact le_rfl
    · positivity

theorem summable_rawPhaseProgressionMeanTerm_pos {k Q : ℕ}
    (hk : 0 < k) (hQ : 0 < Q) (A : ℕ) :
    Summable (rawPhaseProgressionMeanTerm k Q A) := by
  have hs := (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k + 1)).mul_left (Q : ℝ)
  apply Summable.of_nonneg_of_le (fun d => (rawPhaseProgressionMeanTerm_bounds_pos hQ A d).1)
    (fun d => (rawPhaseProgressionMeanTerm_bounds_pos hQ A d).2)
  simpa only [mul_one_div] using hs

theorem one_le_rawPhaseProgressionMean_pos {k Q : ℕ}
    (hk : 0 < k) (hQ : 0 < Q) (A : ℕ) :
    1 ≤ rawPhaseProgressionMean k Q A := by
  have hh := (summable_rawPhaseProgressionMeanTerm_pos hk hQ A).le_tsum 1
    (fun d _ => (rawPhaseProgressionMeanTerm_bounds_pos hQ A d).1)
  simpa [rawPhaseProgressionMean, rawPhaseProgressionMeanTerm, rawPhaseDivisorTerm] using hh

theorem rawPhase_cesaro_progression_pos {k Q A : ℕ}
    (hk : 0 < k) (hQ : 0 < Q) (hA : 0 < A) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, rawPhase k (Q * n + A)) / (N : ℝ)) atTop
      (𝓝 (rawPhaseProgressionMean k Q A)) := by
  have hs : Summable (fun d : ℕ => ((Q + A : ℕ) : ℝ) / (d : ℝ) ^ (k + 1)) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k + 1)).mul_left ((Q + A : ℕ) : ℝ)
  have hh := tendsto_tsum_of_dominated_convergence hs
    (fun d => rawPhaseDivisorTerm_cesaro_pos hk Q A d)
    (Eventually.of_forall (fun N d => rawPhaseDivisorTerm_cesaro_bound_pos hk hQ hA d N))
  apply hh.congr'
  apply Eventually.of_forall
  intro N
  dsimp only
  rw [tsum_div_const,
    Summable.tsum_finsetSum (fun n (_hn : n ∈ Finset.range N) =>
      summable_rawPhaseDivisorTerm_of_pos k (by omega : 0 < Q * n + A))]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact (rawPhase_eq_tsum_divisorTerm k (by omega : 0 < Q * n + A)).symm

theorem summable_rawPhaseProgressionMeanTerm_multiples_pos {k Q : ℕ}
    (hk : 0 < k) (hQ : 0 < Q) (A ell : ℕ) :
    Summable (fun d : ℕ =>
      if ell ∣ d then rawPhaseProgressionMeanTerm k Q A d else 0) := by
  exact (summable_rawPhaseProgressionMeanTerm_pos hk hQ A).summable_of_eq_zero_or_self
    (fun d => by by_cases h : ell ∣ d <;> simp [h])

/-- The exact fresh-prime refinement factor holds in every positive degree. -/
theorem rawPhaseProgressionMean_refine_pos {k Q A B ell : ℕ}
    (hk : 0 < k) (hQ : 0 < Q) (hp : ell.Prime)
    (hc : ell.Coprime Q) (hAB : Nat.ModEq Q B A) :
    rawPhaseProgressionMean k (Q * ell) B =
      rawPhaseProgressionMean k Q A *
        (1 - 1 / (ell : ℝ) ^ (k + 1) + if ell ∣ B then 1 / (ell : ℝ) ^ k else 0) := by
  rw [rawPhaseProgressionMean_refine_of_summable
    (summable_rawPhaseProgressionMeanTerm_pos hk hQ B) hp hc,
    rawPhaseProgressionMean_congr k hAB]
  have he : (ell : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  by_cases hB : ell ∣ B
  · simp only [hB, ↓reduceIte, pow_succ]
    field_simp
    ring
  · simp only [hB, ↓reduceIte]
    ring

/-- Actual phase averages on a fresh-prime subprogression. -/
theorem rawPhase_cesaro_refined_progression_pos {k Q : ℕ}
    (hk : 0 < k) (hQ : 0 < Q) (A L v : ℕ)
    (hp : L.Prime) (hcop : L.Coprime Q) (hA : 0 < A) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, rawPhase k (Q * (L * n + v) + A)) / (N : ℝ)) atTop
      (𝓝 (rawPhaseProgressionMean k Q A *
        (1 - 1 / (L : ℝ) ^ (k + 1) + if L ∣ Q * v + A then 1 / (L : ℝ) ^ k else 0))) := by
  have hB : 0 < Q * v + A := by omega
  have hAB : Nat.ModEq Q (Q * v + A) A := by
    unfold Nat.ModEq
    simp
  have hh := rawPhase_cesaro_progression_pos hk (Nat.mul_pos hQ hp.pos) hB
  rw [rawPhaseProgressionMean_refine_pos hk hQ hp hcop hAB] at hh
  simpa only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] using hh

/-- Every positive degree has the unconditional isolated-shift obstruction. -/
theorem rawPhase_isolated_shift_not_tendsto_zero {k : ℕ} (hk : 0 < k)
    {ι : Type*} [Fintype ι] (r : ι → ℕ) (c : ι → ℝ) (i₀ : ι) (Q A : ℕ)
    (hQ : 0 < Q) (hrpos : ∀ i, 0 < r i)
    (hunique : ∀ i, r i = r i₀ → i = i₀) (hc : c i₀ ≠ 0) :
    ¬ Tendsto (fun n : ℕ => ∑ i, c i * rawPhase k (Q * n + A + r i))
      atTop (𝓝 0) := by
  obtain ⟨L, hp, _hQL, _hrL, hcop, v₀, _hv₀, v₁, _hv₁,
    _hbase₀, _hbase₁, hmiss, hhit⟩ :=
    isolatedShift5_exists_fresh_prime_residues r i₀ Q A hQ hrpos
  have hμ : 0 < rawPhaseProgressionMean k Q (A + r i₀) :=
    lt_of_lt_of_le (by norm_num) (one_le_rawPhaseProgressionMean_pos hk hQ (A + r i₀))
  have hLR : (0 : ℝ) < L := by exact_mod_cast hp.pos
  apply isolatedShift5_not_tendsto_zero_of_divisibility_means
    (rawPhase k) r c (fun i => rawPhaseProgressionMean k Q (A + r i)) i₀ Q A L v₀ v₁
    (1 - 1 / (L : ℝ) ^ (k + 1)) (1 / (L : ℝ) ^ k) hp.pos hunique hc hμ
    (by positivity) hmiss hhit
  intro v i
  have hA : 0 < A + r i := by have := hrpos i; omega
  simpa only [Nat.add_assoc] using
    rawPhase_cesaro_refined_progression_pos hk hQ (A + r i) L v hp hcop.symm hA

#print axioms affineCongruence_count_le_quotient
#print axioms summable_rawPhaseDivisorTerm_of_pos
#print axioms rawPhaseDivisorTerm_cesaro_bound_pos
#print axioms rawPhaseProgressionMeanTerm_bounds_pos
#print axioms summable_rawPhaseProgressionMeanTerm_pos
#print axioms one_le_rawPhaseProgressionMean_pos
#print axioms rawPhase_cesaro_progression_pos
#print axioms summable_rawPhaseProgressionMeanTerm_multiples_pos
#print axioms rawPhaseProgressionMean_refine_pos
#print axioms rawPhase_cesaro_refined_progression_pos
#print axioms rawPhase_isolated_shift_not_tendsto_zero

end

end Erdos252
