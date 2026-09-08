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

theorem rawPhase_bounds_sqrt (k n : ℕ) (hn : 0 < n) :
    0 ≤ rawPhase k n ∧ rawPhase k n ≤ 64 * Real.sqrt (n : ℝ) := by
  constructor
  · unfold rawPhase
    positivity
  · exact sigma_normalized_le_sixty_four_sqrt k n hn

/-- The raw divisor phase is sublinear even in degrees zero and one. -/
theorem tendsto_rawPhase_div_nat (k : ℕ) :
    Tendsto (fun n : ℕ => rawPhase k n / (n : ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => 64 * (Real.sqrt (n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_sqrt_nat_div_nat.const_mul (64 : ℝ)
  apply squeeze_zero' (Eventually.of_forall (fun n => by unfold rawPhase; positivity)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hh := div_le_div_of_nonneg_right
    (rawPhase_bounds_sqrt k n (by omega)).2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [mul_div_assoc] using hh

/-- Every fixed coefficient and shift preserves the vanishing ratio limit. -/
theorem dilationGrid_main_term_tendsto_zero (k : ℕ) (e : DilationGridVertex k) (h : ℕ) :
    Tendsto (fun N : ℕ =>
      dilationGridCoefficient k e h * rawPhase k (N + dilationGridShift k e h) /
        ((N + dilationGridShift k e h : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hh := ((tendsto_rawPhase_div_nat k).comp
    (tendsto_add_atTop_nat (dilationGridShift k e h))).const_mul (dilationGridCoefficient k e h)
  simpa only [mul_zero, mul_div_assoc, Function.comp_apply] using hh

/-- The complete actual surviving main term tends to zero. -/
theorem tendsto_dilationGridSurvivingMain (k : ℕ) :
    Tendsto (dilationGridSurvivingMain k) atTop (𝓝 0) := by
  unfold dilationGridSurvivingMain
  have hh := tendsto_finsetSum (Finset.univ : Finset (DilationGridVertex k))
    (fun e _ => tendsto_finsetSum (Finset.Icc 1 (k + 1))
      (fun h _ => dilationGrid_main_term_tendsto_zero k e h))
  simpa only [Finset.sum_const_zero] using hh

/-- Exact difference between one rescaled reciprocal term and its raw term. -/
theorem dilationGrid_rescaling_term_identity (k N : ℕ) (e : DilationGridVertex k)
    {h : ℕ} (hh : h ∈ Finset.Icc 1 (k + 1)) :
    (N : ℝ) * (dilationGridCoefficient k e h * rawPhase k (N + dilationGridShift k e h) /
        ((N + dilationGridShift k e h : ℕ) : ℝ)) -
      dilationGridCoefficient k e h * rawPhase k (N + dilationGridShift k e h) =
    -(dilationGridCoefficient k e h * rawPhase k (N + dilationGridShift k e h) /
      ((N + dilationGridShift k e h : ℕ) : ℝ)) * (dilationGridShift k e h : ℝ) := by
  have hr := dilationGridShift_pos k e (Finset.mem_Icc.mp hh).1
  have hx : ((N + dilationGridShift k e h : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show N + dilationGridShift k e h ≠ 0 by omega)
  field_simp
  push_cast
  ring

/-- Rescaling the whole finite sum gives a finite sum of vanishing terms. -/
theorem dilationGridSurvivor_rescaling_eq_sum (k N : ℕ) :
    (N : ℝ) * dilationGridSurvivingMain k N - dilationGridSurvivor k N =
      ∑ e : DilationGridVertex k, ∑ h ∈ Finset.Icc 1 (k + 1),
        -(dilationGridCoefficient k e h * rawPhase k (N + dilationGridShift k e h) /
          ((N + dilationGridShift k e h : ℕ) : ℝ)) * (dilationGridShift k e h : ℝ) := by
  unfold dilationGridSurvivingMain dilationGridSurvivor
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro h hh
  exact dilationGrid_rescaling_term_identity k N e hh

/-- The difference after multiplying the main expression by `N` tends to zero. -/
theorem tendsto_dilationGridSurvivor_rescaling (k : ℕ) :
    Tendsto (fun N : ℕ =>
      (N : ℝ) * dilationGridSurvivingMain k N - dilationGridSurvivor k N)
      atTop (𝓝 0) := by
  have hh := tendsto_finsetSum (Finset.univ : Finset (DilationGridVertex k))
    (fun e _ => tendsto_finsetSum (Finset.Icc 1 (k + 1))
      (fun h _ => (dilationGrid_main_term_tendsto_zero k e h).neg.mul_const
        (dilationGridShift k e h : ℝ)))
  simpa only [neg_zero, zero_mul, Finset.sum_const_zero,
    ← dilationGridSurvivor_rescaling_eq_sum] using hh

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

#print axioms rawPhase_bounds_sqrt
#print axioms tendsto_rawPhase_div_nat
#print axioms dilationGrid_main_term_tendsto_zero
#print axioms tendsto_dilationGridSurvivingMain
#print axioms dilationGrid_rescaling_term_identity
#print axioms dilationGridSurvivor_rescaling_eq_sum
#print axioms tendsto_dilationGridSurvivor_rescaling
#print axioms dilationGrid_affine_tendsto_atTop
#print axioms tendsto_dilationGridSurvivingMain_progression
#print axioms tendsto_dilationGridSurvivor_rescaling_progression

end

end Erdos252
