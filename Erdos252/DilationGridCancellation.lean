import Erdos252.DilationGrid
import Erdos252.DilationCube
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Symbolic grid cancellation with integer weights and real test functions

The real cube expansion is identified with the actual natural grid. Every
core of degree at most `k` then cancels for arbitrary real-valued test
functions of the shifts, without any regularity premise.
-/

namespace Erdos252

open scoped BigOperators

def dilationGridWeightInt (k : ℕ) (e : DilationGridVertex k) : ℤ :=
  dilationCubeWeight (k + 1) e

theorem dilationGridWeightInt_zero_ne_zero (k : ℕ) :
    dilationGridWeightInt k (dilationGridZero k) ≠ 0 :=
  dilationCubeWeight_zero_ne_zero (k + 1) k

theorem dilationGridMultiplier_real_eq_cube (k : ℕ) (e : DilationGridVertex k) :
    (dilationGridMultiplier k e : ℝ) = (dilationGridBase k : ℝ) +
      ∑ i : Fin k, (dilationGridSpacing k : ℝ) * ((k : ℝ) + 2) ^ i.val * (e i).val := by
  unfold dilationGridMultiplier dilationGridIndex
  push_cast
  simp only [Finset.mul_sum, mul_comm, mul_left_comm]

theorem dilationGridShift_real_eq_cube (k : ℕ) (e : DilationGridVertex k) {h : ℕ}
    (hh : 1 ≤ h) :
    (dilationGridShift k e h : ℝ) = (h : ℝ) * dilationGridBase k +
      ∑ i : Fin k, ((h : ℝ) - (i.val + 1)) *
        ((dilationGridSpacing k : ℝ) * ((k : ℝ) + 2) ^ i.val) * (e i).val := by
  rw [show (dilationGridShift k e h : ℝ) =
      (h : ℝ) * dilationGridMultiplier k e - dilationGridOffset k e from
    eq_sub_of_add_eq (by exact_mod_cast dilationGridShift_add_offset k e hh),
    dilationGridMultiplier_real_eq_cube]
  unfold dilationGridOffset dilationGridWeightedIndex
  push_cast
  simp only [mul_add, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- All lower-order shifted cores cancel on the actual symbolic grid. -/
theorem dilationGrid_core_real_cancel {k h ell : ℕ}
    (hh : h ∈ Finset.Icc 1 k) (hell : ell ≤ k) (g : ℝ → ℝ) :
    (∑ e : DilationGridVertex k, (dilationGridWeightInt k e : ℝ) *
      ((dilationGridMultiplier k e : ℝ) ^ ell * g (dilationGridShift k e h))) = 0 := by
  obtain ⟨hh1, hhk⟩ := Finset.mem_Icc.mp hh
  simp_rw [dilationGridMultiplier_real_eq_cube, dilationGridShift_real_eq_cube k _ hh1]
  exact dilationCube_core (Nat.lt_succ_of_le hell)
    (fun i : Fin k => (dilationGridSpacing k : ℝ) * ((k : ℝ) + 2) ^ i.val)
    (fun i : Fin k => ((h : ℝ) - (i.val + 1)) *
      ((dilationGridSpacing k : ℝ) * ((k : ℝ) + 2) ^ i.val))
    ⟨h - 1, by omega⟩ (by simp [Nat.cast_sub hh1]) g _ _

/-- Actual integer weights cancel every real-valued shifted core through degree `k`. -/
theorem dilationGrid_core_cancel {k h ell : ℕ}
    (hh : h ∈ Finset.Icc 1 k) (hell : ell ≤ k) (g : ℕ → ℝ) :
    (∑ e : DilationGridVertex k, (dilationGridWeightInt k e : ℝ) *
      ((dilationGridMultiplier k e : ℝ) ^ ell * g (dilationGridShift k e h))) = 0 := by
  simpa only [Nat.floor_natCast] using
    dilationGrid_core_real_cancel hh hell (fun z => g ⌊z⌋₊)

/-- In particular, the actual divisor-power terms of every exponent cancel. -/
theorem dilationGrid_sigma_core_cancel (N : ℕ) {k h ell : ℕ}
    (hh : h ∈ Finset.Icc 1 k) (hell : ell ≤ k) :
    (∑ e : DilationGridVertex k, (dilationGridWeightInt k e : ℝ) *
      ((dilationGridMultiplier k e : ℝ) ^ ell *
        ((ArithmeticFunction.sigma k (N + dilationGridShift k e h) : ℝ) /
          ((N + dilationGridShift k e h : ℕ) : ℝ) ^ ell))) = 0 :=
  dilationGrid_core_cancel hh hell
    (fun s => (ArithmeticFunction.sigma k (N + s) : ℝ) / ((N + s : ℕ) : ℝ) ^ ell)

#print axioms dilationGridWeightInt_zero_ne_zero
#print axioms dilationGridMultiplier_real_eq_cube
#print axioms dilationGridShift_real_eq_cube
#print axioms dilationGrid_core_real_cancel
#print axioms dilationGrid_core_cancel
#print axioms dilationGrid_sigma_core_cancel

end Erdos252
