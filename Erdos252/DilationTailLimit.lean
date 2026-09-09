import Erdos252.DilationWeightedTail
import Erdos252.DilationSurvivorBounds
import Erdos252.U5DilationGenericTailBounds
import Erdos252.EventuallyIntegral

/-!
# Rationality forces the generic actual dilation survivor to vanish

The actual expansion error is transported through the CRT quotient indices.
Eventual integrality and the vanishing weighted tail then force a zero limit
of the actual survivor, on one fixed arithmetic progression.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

noncomputable section

private theorem le_progression (k A t : ℕ) : t ≤ A + dilationGridModulus k * t :=
  (Nat.le_mul_of_pos_left t (dilationGridModulus_pos k)).trans (Nat.le_add_left _ _)

/-- The common argument is bounded by one multiplier times its index plus one. -/
theorem dilationGridTailIndex_common_le (k N : ℕ) (e : DilationGridVertex k)
    (hN : dilationGridOffset k e ≤ N)
    (hcong : N ≡ dilationGridOffset k e [MOD (dilationGridMultiplier k e) ^ 2]) :
    (N : ℝ) ≤ (dilationGridMultiplier k e : ℝ) *
      ((dilationGridTailIndex k N e : ℝ) + 1) := by
  have hn : N ≤ dilationGridMultiplier k e * (dilationGridTailIndex k N e + 1) := by
    rw [dilationGridTailIndex_factorization k N e hN hcong (by norm_num : 1 ≤ 1)]
    exact Nat.le_add_right _ _
  exact_mod_cast hn

/-- The actual error at one CRT index stays negligible after multiplication
by the common progression argument. -/
theorem tendsto_dilationGrid_vertex_error_mul (k A : ℕ)
    (hA : DilationGridCongruences k A) (e : DilationGridVertex k) :
    Tendsto (fun t : ℕ => ((A + dilationGridModulus k * t : ℕ) : ℝ) *
      genericDilationTailError5 k (dilationGridTailIndex k (A + dilationGridModulus k * t) e))
      atTop (𝓝 0) := by
  have hindex := tendsto_dilationGridTailIndex k (dilationGridModulus k) A
    (dilationGridModulus_pos k) e
  have hlim : Tendsto (fun t : ℕ => (dilationGridMultiplier k e : ℝ) *
      (((dilationGridTailIndex k (A + dilationGridModulus k * t) e : ℝ) + 1) *
        genericDilationTailError5 k (dilationGridTailIndex k (A + dilationGridModulus k * t) e)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_genericDilationTailError5_mul k).comp hindex).const_mul
        (dilationGridMultiplier k e : ℝ)
  have hnonneg : ∀ᶠ t : ℕ in atTop,
      0 ≤ genericDilationTailError5 k (dilationGridTailIndex k (A + dilationGridModulus k * t) e) := by
    filter_upwards [hindex.eventually (eventually_ge_atTop (k + 1))] with t ht
    exact genericDilationTailError5_nonneg k _ ht
  refine squeeze_zero' (hnonneg.mono fun t ht => mul_nonneg (Nat.cast_nonneg _) ht) ?_ hlim
  filter_upwards [hnonneg, eventually_ge_atTop (dilationGridTailThreshold k 0)] with t ht hlarge
  have hN := dilationGridTailThreshold_offset_le k _ 0 (hlarge.trans (le_progression k A t)) e
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (dilationGridTailIndex_common_le k _ e
    hN (dilationGridCongruences_add_modulus_mul k A t hA e)) ht

/-- Fixed signed weights preserve the vanishing scaled-error limit. -/
theorem tendsto_dilationGridWeightedError_mul (k A : ℕ)
    (hA : DilationGridCongruences k A) :
    Tendsto (fun t : ℕ => ((A + dilationGridModulus k * t : ℕ) : ℝ) *
      dilationGridWeightedError k (A + dilationGridModulus k * t)) atTop (𝓝 0) := by
  simpa only [dilationGridWeightedError, Finset.mul_sum,
    mul_left_comm, mul_assoc, mul_zero, Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.univ : Finset (DilationGridVertex k)) (fun e _ =>
      (tendsto_dilationGrid_vertex_error_mul k A hA e).const_mul
        ((dilationGridWeightInt k e : ℝ) *
          (ArithmeticFunction.sigma k (dilationGridMultiplier k e) : ℝ)))

theorem tendsto_dilationGridWeightedError (k A : ℕ)
    (hA : DilationGridCongruences k A) :
    Tendsto (fun t : ℕ => dilationGridWeightedError k (A + dilationGridModulus k * t))
      atTop (𝓝 0) := by
  have hN := (tendsto_natCast_atTop_atTop (R := ℝ)).comp
    (dilationGrid_affine_tendsto_atTop (dilationGridModulus k) A (dilationGridModulus_pos k))
  refine ((tendsto_dilationGridWeightedError_mul k A hA).div_atTop hN).congr' ?_
  filter_upwards [hN.eventually_ne_atTop 0] with t ht
  exact mul_div_cancel_left₀ _ ht

/-- Beyond the threshold, the weighted main term is the surviving main term
along the whole CRT progression. -/
theorem eventually_dilationGridWeightedMain_eq_surviving {k : ℕ} (hk : 0 < k) (A : ℕ)
    (hA : DilationGridCongruences k A) :
    (fun t : ℕ => dilationGridWeightedMain k (A + dilationGridModulus k * t)) =ᶠ[atTop]
      fun t : ℕ => dilationGridSurvivingMain k (A + dilationGridModulus k * t) := by
  filter_upwards [eventually_ge_atTop (dilationGridTailThreshold k 0)] with t ht
  exact dilationGridWeightedMain_eq_surviving hk _ (ht.trans (le_progression k A t))
    (dilationGridCongruences_add_modulus_mul k A t hA)

theorem tendsto_dilationGridWeightedTail {k : ℕ} (hk : 0 < k) (A : ℕ)
    (hA : DilationGridCongruences k A) :
    Tendsto (fun t : ℕ => dilationGridWeightedTail k (A + dilationGridModulus k * t))
      atTop (𝓝 0) := by
  have hmain := (tendsto_dilationGridSurvivingMain_progression k (dilationGridModulus k) A
    (dilationGridModulus_pos k)).congr'
    (eventually_dilationGridWeightedMain_eq_surviving hk A hA).symm
  simpa only [← dilationGridWeightedTail_eq_main_add_error, add_zero] using
    hmain.add (tendsto_dilationGridWeightedError k A hA)

/-- Rationality forces the actual generic survivor to vanish on a CRT progression. -/
theorem tendsto_dilationGridSurvivor_of_rational {k : ℕ} (hk : 0 < k)
    (hx : ¬ Irrational (alpha k)) (A : ℕ) (hA : DilationGridCongruences k A) :
    Tendsto (fun t : ℕ => dilationGridSurvivor k (A + dilationGridModulus k * t))
      atTop (𝓝 0) := by
  have hz := dilation5_eventually_zero_of_integral_tendsto
    (tendsto_dilationGridWeightedTail hk A hA)
    (eventually_dilationGridWeightedTail_integral_on_progression k hx A)
  have hmain : Tendsto (fun t : ℕ => ((A + dilationGridModulus k * t : ℕ) : ℝ) *
      dilationGridSurvivingMain k (A + dilationGridModulus k * t)) atTop (𝓝 0) := by
    rw [← neg_zero]
    refine (tendsto_dilationGridWeightedError_mul k A hA).neg.congr' ?_
    filter_upwards [hz, eventually_dilationGridWeightedMain_eq_surviving hk A hA] with t ht heq
    rw [← heq, eq_neg_of_add_eq_zero_left
      ((dilationGridWeightedTail_eq_main_add_error k _).symm.trans ht), mul_neg]
  simpa only [sub_sub_cancel, sub_zero] using hmain.sub
    (tendsto_dilationGridSurvivor_rescaling_progression k (dilationGridModulus k) A
      (dilationGridModulus_pos k))

#print axioms dilationGridTailIndex_common_le
#print axioms tendsto_dilationGrid_vertex_error_mul
#print axioms tendsto_dilationGridWeightedError_mul
#print axioms tendsto_dilationGridWeightedError
#print axioms eventually_dilationGridWeightedMain_eq_surviving
#print axioms tendsto_dilationGridWeightedTail
#print axioms tendsto_dilationGridSurvivor_of_rational

end

end Erdos252
