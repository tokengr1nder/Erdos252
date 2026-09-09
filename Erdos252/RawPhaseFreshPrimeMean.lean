import Erdos252.RawPhaseProgressionMean
import Erdos252.IsolatedShiftResidues
import Erdos252.IsolatedShiftMeanContradiction

/-!
# Fresh-prime refinement of divisor-phase means and the isolated-shift obstruction

Refinement by a prime not dividing the old modulus changes the mean by the
exact factor `1 - ell^(-(k+1)) + 1_hit * ell^(-k)`. Two refinements that
separate one isolated shift therefore forbid a zero limit of the weighted
phase sum, in every positive degree.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

noncomputable section

theorem rawPhaseProgressionMeanTerm_mul (k : ℕ) {Q ell : ℕ}
    (hc : ell.Coprime Q) (A d : ℕ) :
    rawPhaseProgressionMeanTerm k Q A (ell * d) =
      rawPhaseProgressionMeanTerm k Q A d / (ell : ℝ) ^ (k + 1) := by
  rw [rawPhaseProgressionMeanTerm_eq_gcd,
    rawPhaseProgressionMeanTerm_eq_gcd, hc.gcd_mul_left_cancel]
  split_ifs
  · push_cast
    rw [mul_pow]
    ring
  · simp

theorem rawPhaseProgressionMean_multiples (k : ℕ) {Q ell : ℕ}
    (hell : 0 < ell) (hc : ell.Coprime Q) (A : ℕ) :
    (∑' d : ℕ, if ell ∣ d then rawPhaseProgressionMeanTerm k Q A d else 0) =
      rawPhaseProgressionMean k Q A / (ell : ℝ) ^ (k + 1) := by
  have hinj : Function.Injective (fun d : ℕ => ell * d) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left hell h
  have hs : Function.support (fun d : ℕ =>
      if ell ∣ d then rawPhaseProgressionMeanTerm k Q A d else 0) ⊆
      Set.range (fun d : ℕ => ell * d) := by
    intro d hd
    obtain ⟨j, rfl⟩ : ell ∣ d := Classical.byContradiction (fun h => hd (by simp [h]))
    exact ⟨j, rfl⟩
  rw [← hinj.tsum_eq hs]
  simp only [dvd_mul_right, ↓reduceIte]
  simp_rw [rawPhaseProgressionMeanTerm_mul k hc]
  rw [tsum_div_const]
  rfl

theorem rawPhaseProgressionMeanTerm_congr (k : ℕ) {Q A B : ℕ}
    (hAB : Nat.ModEq Q B A) (d : ℕ) :
    rawPhaseProgressionMeanTerm k Q B d = rawPhaseProgressionMeanTerm k Q A d := by
  simp only [rawPhaseProgressionMeanTerm_eq_gcd,
    hAB.dvd_iff (Nat.gcd_dvd_right d Q)]

theorem rawPhaseProgressionMeanTerm_refine (k : ℕ) {Q ell : ℕ}
    (hp : ell.Prime) (hc : ell.Coprime Q) (B d : ℕ) :
    rawPhaseProgressionMeanTerm k (Q * ell) B d =
      rawPhaseProgressionMeanTerm k Q B d +
        (if ell ∣ B then (ell : ℝ) - 1 else -1) *
          (if ell ∣ d then rawPhaseProgressionMeanTerm k Q B d else 0) := by
  rw [rawPhaseProgressionMeanTerm_eq_gcd,
    rawPhaseProgressionMeanTerm_eq_gcd, hc.symm.gcd_mul,
    rawPhaseFreshPrime_gcd hp]
  by_cases hd : ell ∣ d
  · simp only [hd, ↓reduceIte]
    have hprod : Nat.gcd d Q * ell ∣ B ↔ Nat.gcd d Q ∣ B ∧ ell ∣ B := by
      exact ⟨fun h => ⟨dvd_of_mul_right_dvd h, dvd_of_mul_left_dvd h⟩,
        fun h => (hc.symm.gcd_left d).mul_dvd_of_dvd_of_dvd h.1 h.2⟩
    by_cases hg : Nat.gcd d Q ∣ B <;> by_cases hB : ell ∣ B <;>
      simp only [hg, hB, hprod, and_self, and_false, false_and, ↓reduceIte]
    all_goals push_cast; ring
  · simp only [hd, ↓reduceIte, Nat.mul_one, mul_zero, add_zero]

theorem rawPhaseProgressionMean_congr (k : ℕ) {Q A B : ℕ}
    (hAB : Nat.ModEq Q B A) :
    rawPhaseProgressionMean k Q B = rawPhaseProgressionMean k Q A := by
  unfold rawPhaseProgressionMean
  exact tsum_congr (rawPhaseProgressionMeanTerm_congr k hAB)

/-- The exact fresh-prime refinement factor holds in every positive degree. -/
theorem rawPhaseProgressionMean_refine {k Q A B ell : ℕ} (hk : 0 < k) (hQ : 0 < Q)
    (hp : ell.Prime) (hc : ell.Coprime Q) (hAB : Nat.ModEq Q B A) :
    rawPhaseProgressionMean k (Q * ell) B =
      rawPhaseProgressionMean k Q A *
        (1 - 1 / (ell : ℝ) ^ (k + 1) + if ell ∣ B then 1 / (ell : ℝ) ^ k else 0) := by
  have hs := summable_rawPhaseProgressionMeanTerm hk hQ B
  have hm : Summable (fun d => if ell ∣ d then rawPhaseProgressionMeanTerm k Q B d else 0) :=
    hs.summable_of_eq_zero_or_self (fun d => by by_cases h : ell ∣ d <;> simp [h])
  rw [← rawPhaseProgressionMean_congr k hAB]
  change (∑' d, rawPhaseProgressionMeanTerm k (Q * ell) B d) = _
  simp_rw [rawPhaseProgressionMeanTerm_refine k hp hc B]
  rw [hs.tsum_add (hm.mul_left _), tsum_mul_left,
    rawPhaseProgressionMean_multiples k hp.pos hc]
  change rawPhaseProgressionMean k Q B + _ = _
  have he : (ell : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  split_ifs <;> simp only [pow_succ] <;> field_simp <;> ring

/-- Actual phase averages on a fresh-prime subprogression. -/
theorem rawPhase_cesaro_refined_progression {k Q : ℕ}
    (hk : 0 < k) (hQ : 0 < Q) (A L v : ℕ)
    (hp : L.Prime) (hcop : L.Coprime Q) (hA : 0 < A) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, rawPhase k (Q * (L * n + v) + A)) / (N : ℝ)) atTop
      (𝓝 (rawPhaseProgressionMean k Q A *
        (1 - 1 / (L : ℝ) ^ (k + 1) + if L ∣ Q * v + A then 1 / (L : ℝ) ^ k else 0))) := by
  have hAB : Nat.ModEq Q (Q * v + A) A := by
    unfold Nat.ModEq
    simp
  have hh := rawPhase_cesaro_progression hk (Nat.mul_pos hQ hp.pos) (by omega : 0 < Q * v + A)
  rw [rawPhaseProgressionMean_refine hk hQ hp hcop hAB] at hh
  simpa only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] using hh

/-- Every positive degree has the unconditional isolated-shift obstruction. -/
theorem rawPhase_isolated_shift_not_tendsto_zero {k : ℕ} (hk : 0 < k)
    {ι : Type*} [Fintype ι] (r : ι → ℕ) (c : ι → ℝ) (i₀ : ι) (Q A : ℕ)
    (hQ : 0 < Q) (hrpos : ∀ i, 0 < r i)
    (hunique : ∀ i, r i = r i₀ → i = i₀) (hc : c i₀ ≠ 0) :
    ¬ Tendsto (fun n : ℕ => ∑ i, c i * rawPhase k (Q * n + A + r i))
      atTop (𝓝 0) := by
  obtain ⟨L, hp, hcop, v₀, v₁, hmiss, hhit⟩ :=
    isolatedShift5_exists_fresh_prime_residues r i₀ Q A hQ hrpos
  have hLR : (0 : ℝ) < L := by exact_mod_cast hp.pos
  refine isolatedShift5_not_tendsto_zero (rawPhase k) r c
    (fun i => rawPhaseProgressionMean k Q (A + r i)) i₀ Q A L v₀ v₁
    (1 - 1 / (L : ℝ) ^ (k + 1)) (1 / (L : ℝ) ^ k) hp.pos hunique hc
    (lt_of_lt_of_le one_pos (one_le_rawPhaseProgressionMean hk hQ (A + r i₀)))
    (by positivity) hmiss hhit (fun v i => ?_)
  simpa only [Nat.add_assoc] using rawPhase_cesaro_refined_progression hk hQ (A + r i) L v hp
    hcop.symm (by have := hrpos i; omega)

#print axioms rawPhaseProgressionMeanTerm_mul
#print axioms rawPhaseProgressionMean_multiples
#print axioms rawPhaseProgressionMeanTerm_congr
#print axioms rawPhaseProgressionMeanTerm_refine
#print axioms rawPhaseProgressionMean_congr
#print axioms rawPhaseProgressionMean_refine
#print axioms rawPhase_cesaro_refined_progression
#print axioms rawPhase_isolated_shift_not_tendsto_zero

end

end Erdos252
