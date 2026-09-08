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

/-- The common argument is bounded by one multiplier times its index plus one. -/
theorem dilationGridTailIndex_common_le (k N : ℕ) (e : DilationGridVertex k)
    (hN : dilationGridOffset k e ≤ N)
    (hcong : N ≡ dilationGridOffset k e [MOD (dilationGridMultiplier k e) ^ 2]) :
    (N : ℝ) ≤ (dilationGridMultiplier k e : ℝ) *
      ((dilationGridTailIndex k N e : ℝ) + 1) := by
  have hh := dilationGridTailIndex_factorization k N e hN hcong (by norm_num : 1 ≤ 1)
  have hn : N ≤ dilationGridMultiplier k e * (dilationGridTailIndex k N e + 1) := by
    rw [hh]
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
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hnonneg] with t ht
    exact mul_nonneg (Nat.cast_nonneg _) ht
  · filter_upwards [hnonneg, eventually_ge_atTop (dilationGridTailThreshold k 0)] with t ht hlarge
    have htN : t ≤ A + dilationGridModulus k * t := by
      have := dilationGridModulus_pos k
      nlinarith
    have hN := dilationGridTailThreshold_offset_le k _ 0 (hlarge.trans htN) e
    have hb := dilationGridTailIndex_common_le k _ e hN
      (dilationGridCongruences_add_modulus_mul k A t hA e)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hb ht

/-- Fixed signed weights preserve the vanishing scaled-error limit. -/
theorem tendsto_dilationGridWeightedError_mul (k A : ℕ)
    (hA : DilationGridCongruences k A) :
    Tendsto (fun t : ℕ => ((A + dilationGridModulus k * t : ℕ) : ℝ) *
      dilationGridWeightedError k (A + dilationGridModulus k * t)) atTop (𝓝 0) := by
  have hh : Tendsto (fun t : ℕ => ∑ e : DilationGridVertex k,
      ((dilationGridWeightInt k e : ℝ) *
        (ArithmeticFunction.sigma k (dilationGridMultiplier k e) : ℝ)) *
      (((A + dilationGridModulus k * t : ℕ) : ℝ) *
        genericDilationTailError5 k (dilationGridTailIndex k (A + dilationGridModulus k * t) e)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Finset.sum_const_zero] using
      tendsto_finsetSum (Finset.univ : Finset (DilationGridVertex k)) (fun e _ =>
        (tendsto_dilationGrid_vertex_error_mul k A hA e).const_mul
          ((dilationGridWeightInt k e : ℝ) *
            (ArithmeticFunction.sigma k (dilationGridMultiplier k e) : ℝ)))
  apply hh.congr'
  apply Eventually.of_forall
  intro t
  dsimp only
  unfold dilationGridWeightedError
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem tendsto_dilationGridWeightedError (k A : ℕ)
    (hA : DilationGridCongruences k A) :
    Tendsto (fun t : ℕ => dilationGridWeightedError k (A + dilationGridModulus k * t))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℕ => (1 : ℝ) / ((A + dilationGridModulus k * t : ℕ) : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (dilationGrid_affine_tendsto_atTop (dilationGridModulus k) A (dilationGridModulus_pos k))
  have hh : Tendsto (fun t : ℕ =>
      (((A + dilationGridModulus k * t : ℕ) : ℝ) *
        dilationGridWeightedError k (A + dilationGridModulus k * t)) *
          (1 / ((A + dilationGridModulus k * t : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_dilationGridWeightedError_mul k A hA).mul hi
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with t ht
  have hN : ((A + dilationGridModulus k * t : ℕ) : ℝ) ≠ 0 := by
    have hp := dilationGridModulus_pos k
    exact_mod_cast (show A + dilationGridModulus k * t ≠ 0 by nlinarith)
  field_simp

theorem tendsto_dilationGridWeightedMain {k : ℕ} (hk : 0 < k) (A : ℕ)
    (hA : DilationGridCongruences k A) :
    Tendsto (fun t : ℕ => dilationGridWeightedMain k (A + dilationGridModulus k * t))
      atTop (𝓝 0) := by
  apply (tendsto_dilationGridSurvivingMain_progression k (dilationGridModulus k) A
    (dilationGridModulus_pos k)).congr'
  filter_upwards [eventually_ge_atTop (dilationGridTailThreshold k 0)] with t ht
  have htN : t ≤ A + dilationGridModulus k * t := by
    have := dilationGridModulus_pos k
    nlinarith
  exact (dilationGridWeightedMain_eq_surviving hk _ (ht.trans htN)
    (dilationGridCongruences_add_modulus_mul k A t hA)).symm

theorem tendsto_dilationGridWeightedTail {k : ℕ} (hk : 0 < k) (A : ℕ)
    (hA : DilationGridCongruences k A) :
    Tendsto (fun t : ℕ => dilationGridWeightedTail k (A + dilationGridModulus k * t))
      atTop (𝓝 0) := by
  have hh := (tendsto_dilationGridWeightedMain hk A hA).add
    (tendsto_dilationGridWeightedError k A hA)
  simpa only [← dilationGridWeightedTail_eq_main_add_error, add_zero] using hh

theorem eventually_dilationGridWeightedTail_zero {k : ℕ} (hk : 0 < k)
    (hx : ¬ Irrational (alpha k)) (A : ℕ) (hA : DilationGridCongruences k A) :
    ∀ᶠ t : ℕ in atTop, dilationGridWeightedTail k (A + dilationGridModulus k * t) = 0 := by
  exact dilation5_eventually_zero_of_integral_tendsto
    (tendsto_dilationGridWeightedTail hk A hA)
    (eventually_dilationGridWeightedTail_integral_on_progression k hx A)

/-- Rationality forces the actual generic survivor to vanish on a CRT progression. -/
theorem tendsto_dilationGridSurvivor_of_rational {k : ℕ} (hk : 0 < k)
    (hx : ¬ Irrational (alpha k)) (A : ℕ) (hA : DilationGridCongruences k A) :
    Tendsto (fun t : ℕ => dilationGridSurvivor k (A + dilationGridModulus k * t))
      atTop (𝓝 0) := by
  have hz := eventually_dilationGridWeightedTail_zero hk hx A hA
  have hmain : Tendsto (fun t : ℕ => ((A + dilationGridModulus k * t : ℕ) : ℝ) *
      dilationGridSurvivingMain k (A + dilationGridModulus k * t)) atTop (𝓝 0) := by
    have hs : Tendsto (fun t : ℕ =>
        -(((A + dilationGridModulus k * t : ℕ) : ℝ) *
          dilationGridWeightedError k (A + dilationGridModulus k * t))) atTop (𝓝 0) := by
      simpa only [neg_zero] using (tendsto_dilationGridWeightedError_mul k A hA).neg
    apply hs.congr'
    filter_upwards [hz, eventually_ge_atTop (dilationGridTailThreshold k 0)] with t ht hlarge
    have htN : t ≤ A + dilationGridModulus k * t := by
      have := dilationGridModulus_pos k
      nlinarith
    have heq := dilationGridWeightedTail_eq_main_add_error k (A + dilationGridModulus k * t)
    rw [ht, dilationGridWeightedMain_eq_surviving hk _ (hlarge.trans htN)
      (dilationGridCongruences_add_modulus_mul k A t hA)] at heq
    have hh : dilationGridSurvivingMain k (A + dilationGridModulus k * t) =
        -dilationGridWeightedError k (A + dilationGridModulus k * t) := by linarith
    rw [hh]
    ring
  have hd := tendsto_dilationGridSurvivor_rescaling_progression k
    (dilationGridModulus k) A (dilationGridModulus_pos k)
  simpa only [sub_sub_cancel, sub_zero] using hmain.sub hd

#print axioms dilationGridTailIndex_common_le
#print axioms tendsto_dilationGrid_vertex_error_mul
#print axioms tendsto_dilationGridWeightedError_mul
#print axioms tendsto_dilationGridWeightedError
#print axioms tendsto_dilationGridWeightedMain
#print axioms tendsto_dilationGridWeightedTail
#print axioms eventually_dilationGridWeightedTail_zero
#print axioms tendsto_dilationGridSurvivor_of_rational

end

end Erdos252
