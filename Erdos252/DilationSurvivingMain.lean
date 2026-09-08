import Erdos252.DilationGridCancellation
import Erdos252.RawPhaseProgressionMean
import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# The exact final-order survivor in symbolic degree

Finite algebra removes all denominator powers through degree `k`. The
remaining order `k+1` is exactly a weighted reciprocal-shift sum of the
actual normalized divisor phase. No asymptotic estimate is used here.
-/

namespace Erdos252

open scoped BigOperators

noncomputable section

def dilationGridCore (k N h ell : ℕ) : ℝ :=
  ∑ e : DilationGridVertex k, (dilationGridWeightInt k e : ℝ) *
    ((dilationGridMultiplier k e : ℝ) ^ ell *
      ((ArithmeticFunction.sigma k (N + dilationGridShift k e h) : ℝ) /
        ((N + dilationGridShift k e h : ℕ) : ℝ) ^ ell))

def dilationGridFiniteMain (k N : ℕ) : ℝ :=
  ∑ ell ∈ Finset.Icc 1 (k + 1), ∑ h ∈ Finset.Icc 1 (k + 1),
    (Nat.stirlingSecond (ell - 1) (h - 1) : ℝ) * dilationGridCore k N h ell

def dilationGridCoefficient (k : ℕ) (e : DilationGridVertex k) (h : ℕ) : ℝ :=
  (dilationGridWeightInt k e : ℝ) * (dilationGridMultiplier k e : ℝ) ^ (k + 1) *
    (Nat.stirlingSecond k (h - 1) : ℝ)

def dilationGridSurvivingMain (k N : ℕ) : ℝ :=
  ∑ e : DilationGridVertex k, ∑ h ∈ Finset.Icc 1 (k + 1),
    dilationGridCoefficient k e h * rawPhase k (N + dilationGridShift k e h) /
      ((N + dilationGridShift k e h : ℕ) : ℝ)

def dilationGridSurvivor (k N : ℕ) : ℝ :=
  ∑ e : DilationGridVertex k, ∑ h ∈ Finset.Icc 1 (k + 1),
    dilationGridCoefficient k e h * rawPhase k (N + dilationGridShift k e h)

theorem dilationGrid_lower_stirling_cancel (k N : ℕ) {ell h : ℕ}
    (hell : ell ∈ Finset.Icc 1 k) (hh : h ∈ Finset.Icc 1 (k + 1)) :
    (Nat.stirlingSecond (ell - 1) (h - 1) : ℝ) * dilationGridCore k N h ell = 0 := by
  by_cases hhk : h ≤ k
  · rw [show dilationGridCore k N h ell = 0 from
      dilationGrid_sigma_core_cancel N
        (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hh).1, hhk⟩)
        (Finset.mem_Icc.mp hell).2, mul_zero]
  · have hlt : ell - 1 < h - 1 := by
      have := Finset.mem_Icc.mp hell
      have := Finset.mem_Icc.mp hh
      omega
    rw [Nat.stirlingSecond_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul]

theorem dilationGridFiniteMain_eq_final (k N : ℕ) :
    dilationGridFiniteMain k N =
      ∑ h ∈ Finset.Icc 1 (k + 1), (Nat.stirlingSecond k (h - 1) : ℝ) *
        dilationGridCore k N h (k + 1) := by
  unfold dilationGridFiniteMain
  rw [Finset.sum_eq_single (k + 1)]
  · simp only [Nat.add_sub_cancel]
  · intro ell hell hne
    apply Finset.sum_eq_zero
    intro h hh
    apply dilationGrid_lower_stirling_cancel k N _ hh
    have := Finset.mem_Icc.mp hell
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro hnot
    exact False.elim (hnot (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))

/-- The last reciprocal power is the normalized raw phase divided once more. -/
theorem dilationGrid_sigma_div_succ (k x : ℕ) :
    (ArithmeticFunction.sigma k x : ℝ) / (x : ℝ) ^ (k + 1) =
      rawPhase k x / (x : ℝ) := by
  rw [rawPhase, div_div, pow_succ]

/-- Exact expression of the surviving denominator order as raw phases. -/
theorem dilationGridFiniteMain_eq_surviving (k N : ℕ) :
    dilationGridFiniteMain k N = dilationGridSurvivingMain k N := by
  rw [dilationGridFiniteMain_eq_final]
  unfold dilationGridCore dilationGridSurvivingMain
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro h _
  rw [show (Nat.stirlingSecond k (h - 1) : ℝ) *
      ((dilationGridWeightInt k e : ℝ) *
        ((dilationGridMultiplier k e : ℝ) ^ (k + 1) *
          ((ArithmeticFunction.sigma k (N + dilationGridShift k e h) : ℝ) /
            ((N + dilationGridShift k e h : ℕ) : ℝ) ^ (k + 1)))) =
      dilationGridCoefficient k e h *
        ((ArithmeticFunction.sigma k (N + dilationGridShift k e h) : ℝ) /
          ((N + dilationGridShift k e h : ℕ) : ℝ) ^ (k + 1)) by
      unfold dilationGridCoefficient; ring]
  rw [dilationGrid_sigma_div_succ]
  ring

/-- Reordering the expanded vertex sums gives the same finite main term. -/
theorem dilationGridFiniteMain_eq_vertex_sum (k N : ℕ) :
    dilationGridFiniteMain k N =
      ∑ e : DilationGridVertex k, (dilationGridWeightInt k e : ℝ) *
        (∑ h ∈ Finset.Icc 1 (k + 1), ∑ ell ∈ Finset.Icc 1 (k + 1),
          (Nat.stirlingSecond (ell - 1) (h - 1) : ℝ) *
            (dilationGridMultiplier k e : ℝ) ^ ell *
              (ArithmeticFunction.sigma k (N + dilationGridShift k e h) : ℝ) /
                ((N + dilationGridShift k e h : ℕ) : ℝ) ^ ell) := by
  unfold dilationGridFiniteMain dilationGridCore
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext h; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro ell _
  ring

theorem dilationGridCoefficient_zero_succ (k : ℕ) :
    dilationGridCoefficient k (dilationGridZero k) (k + 1) =
      (dilationGridWeightInt k (dilationGridZero k) : ℝ) *
        (dilationGridBase k : ℝ) ^ (k + 1) := by
  simp only [dilationGridCoefficient, dilationGridMultiplier,
    dilationGridIndex_zero, mul_zero, add_zero,
    Nat.add_sub_cancel, Nat.stirlingSecond_self, Nat.cast_one, mul_one]

/-- The isolated final-order coefficient never vanishes. -/
theorem dilationGridCoefficient_zero_succ_ne_zero (k : ℕ) :
    dilationGridCoefficient k (dilationGridZero k) (k + 1) ≠ 0 := by
  rw [dilationGridCoefficient_zero_succ]
  apply mul_ne_zero
  · exact_mod_cast dilationGridWeightInt_zero_ne_zero k
  · apply pow_ne_zero
    exact_mod_cast (dilationGridBase_pos k).ne'

#print axioms dilationGrid_lower_stirling_cancel
#print axioms dilationGridFiniteMain_eq_final
#print axioms dilationGrid_sigma_div_succ
#print axioms dilationGridFiniteMain_eq_surviving
#print axioms dilationGridFiniteMain_eq_vertex_sum
#print axioms dilationGridCoefficient_zero_succ
#print axioms dilationGridCoefficient_zero_succ_ne_zero

end

end Erdos252
