import Erdos252.DilationSurvivingMain
import Erdos252.RawPhasePositiveMean

/-!
# The actual symbolic-degree grid survivor cannot tend to zero

The final shift at the zero vertex is unique and its coefficient is
nonzero. The proved progression-mean obstruction applies in every positive
degree, including degree one, on every positive-step progression.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

noncomputable section

abbrev DilationGridTerm (k : ℕ) :=
  DilationGridVertex k × ↥(Finset.Icc 1 (k + 1) : Finset ℕ)

/-- The distinguished final shift is unique among all vertex-order pairs. -/
theorem dilationGridShift_eq_succ_base_iff {k : ℕ} {e : DilationGridVertex k} {h : ℕ}
    (hh : h ∈ Finset.Icc 1 (k + 1)) :
    dilationGridShift k e h = (k + 1) * dilationGridBase k ↔
      e = dilationGridZero k ∧ h = k + 1 := by
  rcases lt_or_eq_of_le (Finset.mem_Icc.mp hh).2 with hlt | rfl
  · have hne := ne_of_lt (dilationGridShift_lt_succ_base k e (show h ≤ k by omega))
    simp only [hne, ne_of_lt hlt, and_false]
  · simpa only [and_true] using dilationGridShift_succ_eq_iff k e

/-- Flattening the double sum preserves all actual shifts and coefficients. -/
theorem dilationGridSurvivor_eq_sum_terms (k N : ℕ) :
    dilationGridSurvivor k N =
      ∑ i : DilationGridTerm k, dilationGridCoefficient k i.1 i.2 *
        rawPhase k (N + dilationGridShift k i.1 i.2) := by
  simp only [Fintype.sum_prod_type, dilationGridSurvivor]
  exact Finset.sum_congr rfl (fun e _ => (Finset.sum_coe_sort _ _).symm)

/-- The exact final-order survivor has no zero limit along any positive-step
arithmetic progression in any positive divisor-power degree. -/
theorem dilationGridSurvivor_not_tendsto_zero {k : ℕ} (hk : 0 < k)
    (Q A : ℕ) (hQ : 0 < Q) :
    ¬ Tendsto (fun n : ℕ => dilationGridSurvivor k (Q * n + A))
      atTop (𝓝 0) := by
  let i₀ : DilationGridTerm k :=
    ⟨dilationGridZero k, ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩⟩⟩
  have hrpos (i : DilationGridTerm k) : 0 < dilationGridShift k i.1 i.2 :=
    dilationGridShift_pos k i.1 (Finset.mem_Icc.mp i.2.property).1
  have hunique (i : DilationGridTerm k)
      (hi : dilationGridShift k i.1 i.2 = dilationGridShift k i₀.1 i₀.2) : i = i₀ := by
    have hzero : dilationGridShift k i₀.1 i₀.2 = (k + 1) * dilationGridBase k :=
      (dilationGridShift_succ_eq_iff k (dilationGridZero k)).mpr rfl
    rw [hzero] at hi
    have hh := (dilationGridShift_eq_succ_base_iff i.2.property).mp hi
    apply Prod.ext hh.1
    exact Subtype.ext hh.2
  have hc : dilationGridCoefficient k i₀.1 i₀.2 ≠ 0 :=
    dilationGridCoefficient_zero_succ_ne_zero k
  have hh := rawPhase_isolated_shift_not_tendsto_zero hk
    (fun i : DilationGridTerm k => dilationGridShift k i.1 i.2)
    (fun i : DilationGridTerm k => dilationGridCoefficient k i.1 i.2)
    i₀ Q A hQ hrpos hunique hc
  simpa only [dilationGridSurvivor_eq_sum_terms] using hh

#print axioms dilationGridShift_eq_succ_base_iff
#print axioms dilationGridSurvivor_eq_sum_terms
#print axioms dilationGridSurvivor_not_tendsto_zero

end

end Erdos252
