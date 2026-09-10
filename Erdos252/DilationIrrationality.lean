import Erdos252.DilationSurvivingMain
import Erdos252.ProgressionMean

/-!
# Irrationality of the divisor-sum factorial series in every positive degree

The final shift at the zero vertex is unique and its coefficient is nonzero,
so rationality would force the actual fixed-grid survivor to tend to zero.
The unconditional arithmetic-progression mean theorem forbids that limit.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

abbrev GridTerm (k : ℕ) := GridVertex k × Fin (k + 1)

/-- Flattening the double sum preserves all actual shifts and coefficients. -/
theorem survivor_eq_sum_terms (k N : ℕ) :
    survivor k N = ∑ i : GridTerm k, gridCoeff k i.1 i.2 * phase k (N + gridShift k i.1 i.2) := by
  simp only [Fintype.sum_prod_type, survivor, ← Fin.sum_univ_eq_sum_range]

/-- The exact final-order survivor has no zero limit along any positive-step
arithmetic progression in any positive divisor-power degree. -/
theorem survivor_not_tendsto_zero {k : ℕ} (hk : 0 < k) (Q A : ℕ) (hQ : 0 < Q) :
    ¬ Tendsto (fun n : ℕ => survivor k (Q * n + A)) atTop (𝓝 0) := by
  let i₀ : GridTerm k := ⟨gridZero k, Fin.last k⟩
  have hunique (i : GridTerm k) (hi : gridShift k i.1 i.2 = gridShift k i₀.1 i₀.2) : i = i₀ := by
    obtain ⟨he, hj⟩ := (gridShift_eq_succ_base_iff i.1 (Nat.lt_succ_iff.mp i.2.isLt)).mp
      (hi.trans ((gridShift_eq_succ_base_iff i₀.1 le_rfl).mpr ⟨rfl, rfl⟩))
    exact Prod.ext he (Fin.ext hj)
  simpa only [survivor_eq_sum_terms] using isolated_shift_not_tendsto_zero hk
    (fun i : GridTerm k => gridShift k i.1 i.2) (fun i : GridTerm k => gridCoeff k i.1 i.2)
    i₀ Q A hQ (fun i => gridShift_pos k i.1 i.2) hunique (gridCoeff_zero_ne_zero k)

theorem irrational_alpha_pos {k : ℕ} (hk : 0 < k) : Irrational (alpha k) := by
  by_contra hx
  obtain ⟨A, hA⟩ := grid_exists_crt k
  have hz := tendsto_survivor_of_rational hk hx A hA
  apply survivor_not_tendsto_zero hk (gridModulus k) A (gridModulus_pos k)
  simpa only [Nat.add_comm] using hz

end Erdos252
