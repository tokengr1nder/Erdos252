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
  simpa only [Finset.sum_comm, div_eq_mul_inv, Finset.sum_mul,
    ← Finset.mul_sum, mul_assoc] using
    tendsto_finsetSum Finset.univ (fun i _ => (hμ i).const_mul (c i))

/-- A positive-step subprogression preserves a sequence limit and its Cesaro limit. -/
theorem sequenceCesaro5_subprogression_tendsto {f : ℕ → ℝ} {a : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) {L : ℕ} (hL : 0 < L) (v : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, f (L * n + v)) / (N : ℝ)) atTop (𝓝 a) := by
  have hlin : Tendsto (fun n : ℕ => L * n + v) atTop atTop :=
    (tendsto_add_atTop_nat v).comp (tendsto_id.const_mul_atTop' hL)
  simpa only [div_eq_mul_inv, mul_comm, Function.comp_def] using (hf.comp hlin).cesaro

/-- An isolated shift contributes exactly its own weighted change in mean. -/
theorem isolatedShift5_weighted_mean_difference {ι : Type*} [Fintype ι]
    (r : ι → ℕ) (c μ : ι → ℝ) (i₀ : ι) (β κ : ℝ)
    (hunique : ∀ i, r i = r i₀ → i = i₀) :
    (∑ i, c i * (μ i * (β + if r i = r i₀ then κ else 0))) -
        (∑ i, c i * (μ i * β)) = c i₀ * μ i₀ * κ := by
  classical
  have hr (i : ι) : r i = r i₀ ↔ i = i₀ := ⟨hunique i, fun h => h ▸ rfl⟩
  simp_rw [mul_add, Finset.sum_add_distrib, add_sub_cancel_left, mul_ite, mul_zero, hr]
  simp [mul_assoc]

/-- Two explicitly separated refinement means rule out a zero limit of the
original weighted sequence. The first residue misses every shift and the
second residue hits exactly the distinguished shift; both individual Cesaro
limits occur in the hypotheses. -/
theorem isolatedShift5_not_tendsto_zero {ι : Type*} [Fintype ι]
    (f : ℕ → ℝ) (r : ι → ℕ) (c μ : ι → ℝ) (i₀ : ι)
    (Q A L v₀ v₁ : ℕ) (β κ : ℝ) (hL : 0 < L)
    (hunique : ∀ i, r i = r i₀ → i = i₀)
    (hc : c i₀ ≠ 0) (hμ : 0 < μ i₀) (hκ : 0 < κ)
    (hmiss : ∀ i, ¬ L ∣ Q * v₀ + A + r i)
    (hhit : ∀ i, L ∣ Q * v₁ + A + r i ↔ r i = r i₀)
    (hmean : ∀ v i, Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, f (Q * (L * n + v) + A + r i)) / (N : ℝ))
      atTop (𝓝 (μ i * (β + if L ∣ Q * v + A + r i then κ else 0)))) :
    ¬ Tendsto (fun n : ℕ => ∑ i, c i * f (Q * n + A + r i)) atTop (𝓝 0) := by
  intro hz
  have heq (v : ℕ) := tendsto_nhds_unique (finiteWeightedCesaro5 _ c _ (hmean v))
    (sequenceCesaro5_subprogression_tendsto hz hL v)
  have h₀ := heq v₀
  have h₁ := heq v₁
  simp only [hmiss, hhit, ↓reduceIte, add_zero] at h₀ h₁
  have hdiff := isolatedShift5_weighted_mean_difference r c μ i₀ β κ hunique
  rw [h₀, h₁, sub_self] at hdiff
  exact (mul_ne_zero (mul_ne_zero hc hμ.ne') hκ.ne') hdiff.symm

#print axioms finiteWeightedCesaro5
#print axioms sequenceCesaro5_subprogression_tendsto
#print axioms isolatedShift5_weighted_mean_difference
#print axioms isolatedShift5_not_tendsto_zero

end

end Erdos252
