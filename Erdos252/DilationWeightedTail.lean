import Erdos252.DilationGridTailIndex
import Erdos252.DilationSurvivorBounds
import Erdos252.U5DilationGenericTail

/-!
# Actual weighted factorial tails on every positive-dimensional grid

The finite sums use exactly the integer weights already checked in the
symbolic cancellation argument. All tails refer to the original `alpha k`.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

noncomputable section

def dilationGridWeightedTail (k N : ℕ) : ℝ :=
  ∑ e : DilationGridVertex k, (dilationGridWeightInt k e : ℝ) *
    (ArithmeticFunction.sigma k (dilationGridMultiplier k e) : ℝ) *
      genericScaledFullTail5 k (dilationGridTailIndex k N e + 1)

def dilationGridWeightedMain (k N : ℕ) : ℝ :=
  ∑ e : DilationGridVertex k, (dilationGridWeightInt k e : ℝ) *
    (ArithmeticFunction.sigma k (dilationGridMultiplier k e) : ℝ) *
      genericDilationTailMain5 k (dilationGridTailIndex k N e)

def dilationGridWeightedError (k N : ℕ) : ℝ :=
  ∑ e : DilationGridVertex k, (dilationGridWeightInt k e : ℝ) *
    (ArithmeticFunction.sigma k (dilationGridMultiplier k e) : ℝ) *
      genericDilationTailError5 k (dilationGridTailIndex k N e)

theorem dilationGridWeightedTail_eq_main_add_error (k N : ℕ) :
    dilationGridWeightedTail k N = dilationGridWeightedMain k N +
      dilationGridWeightedError k N := by
  unfold dilationGridWeightedTail dilationGridWeightedMain dilationGridWeightedError
  simp_rw [genericDilationTail5_expansion, mul_add, Finset.sum_add_distrib]

theorem eventually_dilationGridWeightedTail_integral (k : ℕ)
    (hx : ¬ Irrational (alpha k)) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∃ z : ℤ, dilationGridWeightedTail k N = z := by
  classical
  obtain ⟨K, hK⟩ := eventually_genericScaledFullTail5_integral k hx
  refine ⟨dilationGridTailThreshold k K, fun N hN => ?_⟩
  choose z hz using fun e : DilationGridVertex k =>
    hK _ ((dilationGridTailIndex_ge k N K hN e).trans (Nat.le_succ _))
  exact ⟨∑ e : DilationGridVertex k, dilationGridWeightInt k e *
    (ArithmeticFunction.sigma k (dilationGridMultiplier k e) : ℤ) * z e,
    by simp only [dilationGridWeightedTail, hz, Int.cast_sum, Int.cast_mul, Int.cast_natCast]⟩

theorem eventually_dilationGridWeightedTail_integral_on_progression (k : ℕ)
    (hx : ¬ Irrational (alpha k)) (A : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∃ z : ℤ,
      dilationGridWeightedTail k (A + dilationGridModulus k * t) = z := by
  obtain ⟨T, hT⟩ := eventually_dilationGridWeightedTail_integral k hx
  exact (dilationGrid_affine_tendsto_atTop _ A (dilationGridModulus_pos k)).eventually
    ((eventually_ge_atTop T).mono hT)

/-- Every actual quotient index tends to infinity on a positive-step progression. -/
theorem tendsto_dilationGridTailIndex (k Q A : ℕ) (hQ : 0 < Q)
    (e : DilationGridVertex k) :
    Tendsto (fun t : ℕ => dilationGridTailIndex k (A + Q * t) e) atTop atTop :=
  (Nat.tendsto_div_const_atTop (dilationGridMultiplier_pos k e).ne').comp
    ((tendsto_sub_atTop_nat (dilationGridOffset k e)).comp
      (dilationGrid_affine_tendsto_atTop Q A hQ))

/-- Exact rescaling of the generic finite main term at one actual grid vertex. -/
theorem dilationGridTailMain_rescale {k : ℕ} (hk : 0 < k) (N : ℕ)
    (e : DilationGridVertex k) (hN : dilationGridOffset k e ≤ N)
    (hcong : N ≡ dilationGridOffset k e [MOD (dilationGridMultiplier k e) ^ 2]) :
    (ArithmeticFunction.sigma k (dilationGridMultiplier k e) : ℝ) *
        genericDilationTailMain5 k (dilationGridTailIndex k N e) =
      ∑ h ∈ Finset.Icc 1 (k + 1), ∑ ell ∈ Finset.Icc 1 (k + 1),
        (Nat.stirlingSecond (ell - 1) (h - 1) : ℝ) *
          (dilationGridMultiplier k e : ℝ) ^ ell *
            (ArithmeticFunction.sigma k (N + dilationGridShift k e h) : ℝ) /
              ((N + dilationGridShift k e h : ℕ) : ℝ) ^ ell := by
  rw [genericDilationTailMain5_eq_Icc]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun h hh => Finset.sum_congr rfl (fun ell _ => ?_))
  simpa only [mul_assoc, mul_left_comm, mul_div_assoc] using
    congrArg ((Nat.stirlingSecond (ell - 1) (h - 1) : ℝ) * ·)
      (dilationGridTailIndex_term_rescale hk N e hN hcong hh ell)

/-- Cancellation identifies the actual weighted main term with the actual survivor main term. -/
theorem dilationGridWeightedMain_eq_surviving {k : ℕ} (hk : 0 < k) (N : ℕ)
    (hN : dilationGridTailThreshold k 0 ≤ N) (hcong : DilationGridCongruences k N) :
    dilationGridWeightedMain k N = dilationGridSurvivingMain k N := by
  rw [← dilationGridFiniteMain_eq_surviving, dilationGridFiniteMain_eq_vertex_sum]
  unfold dilationGridWeightedMain
  apply Finset.sum_congr rfl
  intro e he
  rw [mul_assoc, dilationGridTailMain_rescale hk N e
    (dilationGridTailThreshold_offset_le k N 0 hN e) (hcong e)]

#print axioms dilationGridWeightedTail_eq_main_add_error
#print axioms eventually_dilationGridWeightedTail_integral
#print axioms eventually_dilationGridWeightedTail_integral_on_progression
#print axioms tendsto_dilationGridTailIndex
#print axioms dilationGridTailMain_rescale
#print axioms dilationGridWeightedMain_eq_surviving

end

end Erdos252
