import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A separated pair of refinement means contradicts a zero limit

This module is independent of divisor arithmetic. It treats the two individual
refinement means as explicit hypotheses and proves the resulting obstruction
to a zero limit of a finite weighted sum. A unique shift with a nonzero
coefficient contributes a nonzero difference between the two means.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Finite weighted sums commute with limits of their Cesaro averages. -/
theorem finiteWeightedCesaro5 {ι : Type*} [Fintype ι]
    (f : ι → ℕ → ℝ) (c μ : ι → ℝ)
    (hμ : ∀ i, Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, f i n) / (N : ℝ)) atTop (𝓝 (μ i))) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, ∑ i, c i * f i n) / (N : ℝ)) atTop
      (𝓝 (∑ i, c i * μ i)) := by
  have hh := tendsto_finsetSum Finset.univ (fun i _ => (hμ i).const_mul (c i))
  apply hh.congr'
  apply Eventually.of_forall
  intro N
  dsimp only
  rw [Finset.sum_comm, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  ring

/-- A convergent sequence has the same limit under normalized finite averaging. -/
theorem sequenceCesaro5_tendsto {f : ℕ → ℝ} {a : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f n) / (N : ℝ))
      atTop (𝓝 a) := by
  simpa only [div_eq_mul_inv, mul_comm] using hf.cesaro

/-- A positive-step subprogression preserves a sequence limit and its Cesaro limit. -/
theorem sequenceCesaro5_subprogression_tendsto {f : ℕ → ℝ} {a : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) {L : ℕ} (hL : 0 < L) (v : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, f (L * n + v)) / (N : ℝ)) atTop (𝓝 a) := by
  have hlin : Tendsto (fun n : ℕ => L * n + v) atTop atTop :=
    (tendsto_add_atTop_nat v).comp (tendsto_id.const_mul_atTop' hL)
  exact sequenceCesaro5_tendsto (hf.comp hlin)

/-- An isolated shift contributes exactly its own weighted change in mean. -/
theorem isolatedShift5_weighted_mean_difference {ι : Type*} [Fintype ι]
    (r : ι → ℕ) (c μ : ι → ℝ) (i₀ : ι) (β κ : ℝ)
    (hunique : ∀ i, r i = r i₀ → i = i₀) :
    (∑ i, c i * (μ i * (β + if r i = r i₀ then κ else 0))) -
        (∑ i, c i * (μ i * β)) = c i₀ * μ i₀ * κ := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ i, if i = i₀ then c i₀ * μ i₀ * κ else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = i₀
      · subst i
        simp only [↓reduceIte]
        ring
      · have hr : r i ≠ r i₀ := fun h => hi (hunique i h)
        simp only [hr, hi, ↓reduceIte, add_zero, sub_self]
    _ = _ := by simp

/-- Two explicitly separated refinement means rule out a zero limit of the
original weighted sequence. No arithmetic distribution theorem is assumed
implicitly: both individual Cesaro limits occur in the hypotheses. -/
theorem isolatedShift5_not_tendsto_zero {ι : Type*} [Fintype ι]
    (f : ℕ → ℝ) (r : ι → ℕ) (c μ : ι → ℝ) (i₀ : ι)
    (Q A L v₀ v₁ : ℕ) (β κ : ℝ) (hL : 0 < L)
    (hunique : ∀ i, r i = r i₀ → i = i₀)
    (hc : c i₀ ≠ 0) (hμ : 0 < μ i₀) (hκ : 0 < κ)
    (hmean₀ : ∀ i, Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, f (Q * (L * n + v₀) + A + r i)) / (N : ℝ))
      atTop (𝓝 (μ i * β)))
    (hmean₁ : ∀ i, Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, f (Q * (L * n + v₁) + A + r i)) / (N : ℝ))
      atTop (𝓝 (μ i * (β + if r i = r i₀ then κ else 0)))) :
    ¬ Tendsto (fun n : ℕ => ∑ i, c i * f (Q * n + A + r i))
      atTop (𝓝 0) := by
  intro hz
  have hzero₀ := sequenceCesaro5_subprogression_tendsto hz hL v₀
  have hzero₁ := sequenceCesaro5_subprogression_tendsto hz hL v₁
  have hweighted₀ := finiteWeightedCesaro5
    (fun i n => f (Q * (L * n + v₀) + A + r i)) c
    (fun i => μ i * β) hmean₀
  have hweighted₁ := finiteWeightedCesaro5
    (fun i n => f (Q * (L * n + v₁) + A + r i)) c
    (fun i => μ i * (β + if r i = r i₀ then κ else 0)) hmean₁
  have heq₀ : (∑ i, c i * (μ i * β)) = 0 :=
    tendsto_nhds_unique hweighted₀ hzero₀
  have heq₁ : (∑ i, c i * (μ i * (β + if r i = r i₀ then κ else 0))) = 0 :=
    tendsto_nhds_unique hweighted₁ hzero₁
  have hdiff := isolatedShift5_weighted_mean_difference r c μ i₀ β κ hunique
  rw [heq₀, heq₁, sub_self] at hdiff
  exact (mul_ne_zero (mul_ne_zero hc hμ.ne') hκ.ne') hdiff.symm

/-- Divisibility-based refinement formulas specialize directly to the abstract
isolated-shift contradiction. The first residue misses every shift and the
second residue hits exactly the distinguished shift. -/
theorem isolatedShift5_not_tendsto_zero_of_divisibility_means
    {ι : Type*} [Fintype ι]
    (f : ℕ → ℝ) (r : ι → ℕ) (c μ : ι → ℝ) (i₀ : ι)
    (Q A L v₀ v₁ : ℕ) (β κ : ℝ) (hL : 0 < L)
    (hunique : ∀ i, r i = r i₀ → i = i₀)
    (hc : c i₀ ≠ 0) (hμ : 0 < μ i₀) (hκ : 0 < κ)
    (hmiss : ∀ i, ¬ L ∣ Q * v₀ + A + r i)
    (hhit : ∀ i, L ∣ Q * v₁ + A + r i ↔ r i = r i₀)
    (hmean : ∀ v i, Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, f (Q * (L * n + v) + A + r i)) / (N : ℝ))
      atTop (𝓝 (μ i * (β + if L ∣ Q * v + A + r i then κ else 0)))) :
    ¬ Tendsto (fun n : ℕ => ∑ i, c i * f (Q * n + A + r i))
      atTop (𝓝 0) := by
  apply isolatedShift5_not_tendsto_zero f r c μ i₀ Q A L v₀ v₁ β κ hL
    hunique hc hμ hκ
  · intro i
    simpa only [hmiss i, ↓reduceIte, add_zero] using hmean v₀ i
  · intro i
    simpa only [hhit i] using hmean v₁ i

#print axioms finiteWeightedCesaro5
#print axioms sequenceCesaro5_tendsto
#print axioms sequenceCesaro5_subprogression_tendsto
#print axioms isolatedShift5_weighted_mean_difference
#print axioms isolatedShift5_not_tendsto_zero
#print axioms isolatedShift5_not_tendsto_zero_of_divisibility_means

end

end Erdos252
