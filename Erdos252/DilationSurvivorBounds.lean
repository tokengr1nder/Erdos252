import Erdos252.DilationSurvivingMain
import Erdos252.DilationGrowth

/-!
# Vanishing limits of the generic surviving main expression

The normalized divisor sum is at most a fixed square-root majorant, in every
natural degree. After division by its positive argument, each individual
shifted term therefore tends to zero. Finite summation gives both required
limits without any uniform boundedness assumption on the raw phase itself.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The raw divisor phase is sublinear even in degrees zero and one. -/
theorem tendsto_rawPhase_div_nat (k : ℕ) :
    Tendsto (fun n : ℕ => rawPhase k n / (n : ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => 64 * (Real.sqrt (n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_sqrt_nat_div_nat.const_mul (64 : ℝ)
  refine squeeze_zero' (Eventually.of_forall fun n => by unfold rawPhase; positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa only [rawPhase, mul_div_assoc] using div_le_div_of_nonneg_right
    (sigma_normalized_le_sixty_four_sqrt k n (by omega)) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

/-- Every fixed coefficient and shift preserves the vanishing ratio limit. -/
theorem dilationGrid_main_term_tendsto_zero (k : ℕ) (e : DilationGridVertex k) (h : ℕ) :
    Tendsto (fun N : ℕ =>
      dilationGridCoefficient k e h * rawPhase k (N + dilationGridShift k e h) /
        ((N + dilationGridShift k e h : ℕ) : ℝ)) atTop (𝓝 0) := by
  simpa only [mul_zero, mul_div_assoc, Function.comp_apply] using
    ((tendsto_rawPhase_div_nat k).comp
      (tendsto_add_atTop_nat (dilationGridShift k e h))).const_mul (dilationGridCoefficient k e h)

/-- The complete actual surviving main term tends to zero. -/
theorem tendsto_dilationGridSurvivingMain (k : ℕ) :
    Tendsto (dilationGridSurvivingMain k) atTop (𝓝 0) := by
  unfold dilationGridSurvivingMain
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.univ : Finset (DilationGridVertex k))
      (fun e _ => tendsto_finsetSum (Finset.Icc 1 (k + 1))
        (fun h _ => dilationGrid_main_term_tendsto_zero k e h))

/-- Multiplying the main expression by `N` differs from the survivor by a
finite sum of vanishing terms. -/
theorem tendsto_dilationGridSurvivor_rescaling (k : ℕ) :
    Tendsto (fun N : ℕ =>
      (N : ℝ) * dilationGridSurvivingMain k N - dilationGridSurvivor k N)
      atTop (𝓝 0) := by
  have hh := tendsto_finsetSum (Finset.univ : Finset (DilationGridVertex k))
    (fun e _ => tendsto_finsetSum (Finset.Icc 1 (k + 1))
      (fun h _ => (dilationGrid_main_term_tendsto_zero k e h).neg.mul_const
        (dilationGridShift k e h : ℝ)))
  simp only [neg_zero, zero_mul, Finset.sum_const_zero] at hh
  refine hh.congr fun N => ?_
  unfold dilationGridSurvivingMain dilationGridSurvivor
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun h hh => ?_
  have hx : ((N + dilationGridShift k e h : ℕ) : ℝ) ≠ 0 := by
    have := dilationGridShift_pos k e (Finset.mem_Icc.mp hh).1
    exact_mod_cast (show N + dilationGridShift k e h ≠ 0 by omega)
  field_simp
  push_cast
  ring

theorem dilationGrid_affine_tendsto_atTop (Q A : ℕ) (hQ : 0 < Q) :
    Tendsto (fun t : ℕ => A + Q * t) atTop atTop := by
  simpa only [Nat.add_comm, Function.comp_def, id_eq] using
    (tendsto_add_atTop_nat A).comp (tendsto_id.const_mul_atTop' hQ)

theorem tendsto_dilationGridSurvivingMain_progression (k Q A : ℕ) (hQ : 0 < Q) :
    Tendsto (fun t : ℕ => dilationGridSurvivingMain k (A + Q * t)) atTop (𝓝 0) :=
  (tendsto_dilationGridSurvivingMain k).comp (dilationGrid_affine_tendsto_atTop Q A hQ)

theorem tendsto_dilationGridSurvivor_rescaling_progression (k Q A : ℕ) (hQ : 0 < Q) :
    Tendsto (fun t : ℕ => ((A + Q * t : ℕ) : ℝ) *
      dilationGridSurvivingMain k (A + Q * t) - dilationGridSurvivor k (A + Q * t))
      atTop (𝓝 0) :=
  (tendsto_dilationGridSurvivor_rescaling k).comp (dilationGrid_affine_tendsto_atTop Q A hQ)

#print axioms tendsto_rawPhase_div_nat
#print axioms dilationGrid_main_term_tendsto_zero
#print axioms tendsto_dilationGridSurvivingMain
#print axioms tendsto_dilationGridSurvivor_rescaling
#print axioms dilationGrid_affine_tendsto_atTop
#print axioms tendsto_dilationGridSurvivingMain_progression
#print axioms tendsto_dilationGridSurvivor_rescaling_progression

end

end Erdos252
