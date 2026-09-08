import Erdos252.DilationGrid
import Erdos252.DilationCube
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Real.Basic

/-!
# Symbolic grid cancellation with integer weights and real test functions

The rational cube expansion is identified with the actual natural grid.
Indicator tests then show that the total rational coefficient at each
shift vanishes. Regrouping by shift extends the cancellation to arbitrary
real-valued test functions, without any regularity premise.
-/

namespace Erdos252

open scoped BigOperators

def dilationGridWeightInt (k : ℕ) (e : DilationGridVertex k) : ℤ :=
  dilationCubeWeightInt (k + 1) e

theorem dilationGridWeightInt_rat (k : ℕ) (e : DilationGridVertex k) :
    (dilationGridWeightInt k e : ℚ) = dilationCubeWeight (k + 1) e :=
  dilationCubeWeightInt_rat (k + 1) e

theorem dilationGridWeightInt_zero_ne_zero (k : ℕ) :
    dilationGridWeightInt k (dilationGridZero k) ≠ 0 :=
  dilationCubeWeightInt_zero_ne_zero (k + 1) k

theorem dilationGridMultiplier_rat_eq_cube (k : ℕ) (e : DilationGridVertex k) :
    (dilationGridMultiplier k e : ℚ) = (dilationGridBase k : ℚ) +
      ∑ i : Fin k, (dilationGridSpacing k : ℚ) * ((k : ℚ) + 2) ^ i.val * (e i).val := by
  unfold dilationGridMultiplier dilationGridIndex
  push_cast
  simp only [Finset.mul_sum, mul_comm, mul_left_comm]

theorem dilationGridOffset_rat_eq_cube (k : ℕ) (e : DilationGridVertex k) :
    (dilationGridOffset k e : ℚ) =
      ∑ i : Fin k, ((i.val : ℚ) + 1) * (dilationGridSpacing k : ℚ) *
        ((k : ℚ) + 2) ^ i.val * (e i).val := by
  unfold dilationGridOffset dilationGridWeightedIndex
  push_cast
  simp only [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem dilationGridShift_rat_eq (k : ℕ) (e : DilationGridVertex k) {h : ℕ}
    (hh : 1 ≤ h) :
    (dilationGridShift k e h : ℚ) =
      (h : ℚ) * (dilationGridMultiplier k e : ℚ) - (dilationGridOffset k e : ℚ) := by
  have heq : (dilationGridShift k e h : ℚ) + (dilationGridOffset k e : ℚ) =
      (h : ℚ) * (dilationGridMultiplier k e : ℚ) := by
    exact_mod_cast dilationGridShift_add_offset k e hh
  linarith

/-- All lower-order shifted cores cancel on the actual symbolic grid. -/
theorem dilationGrid_core_rat_cancel {k h ell : ℕ}
    (hh : h ∈ Finset.Icc 1 k) (hell : ell ≤ k) (g : ℚ → ℚ) :
    (∑ e : DilationGridVertex k, dilationCubeWeight (k + 1) e *
      ((dilationGridMultiplier k e : ℚ) ^ ell * g (dilationGridShift k e h : ℚ))) = 0 := by
  have hh1 := (Finset.mem_Icc.mp hh).1
  have hhk := (Finset.mem_Icc.mp hh).2
  let i : Fin k := ⟨h - 1, by omega⟩
  have hi : (i.val : ℚ) + 1 = (h : ℚ) := by
    have hn : i.val + 1 = h := by dsimp [i]; omega
    exact_mod_cast hn
  have hb := dilationCube_core (fun j : Fin k => (j.val : ℚ) + 1)
    (fun j : Fin k => (dilationGridSpacing k : ℚ) * ((k : ℚ) + 2) ^ j.val)
    i (Nat.lt_succ_of_le hell) g (dilationGridBase k : ℚ) 0
  have hoff (e : DilationGridVertex k) :
      (∑ a : Fin k, ((a.val : ℚ) + 1) *
        ((dilationGridSpacing k : ℚ) * ((k : ℚ) + 2) ^ a.val) * (e a).val) =
      (dilationGridOffset k e : ℚ) := by
    simpa only [mul_assoc] using (dilationGridOffset_rat_eq_cube k e).symm
  simp_rw [hi, ← dilationGridMultiplier_rat_eq_cube, zero_add,
    hoff, ← dilationGridShift_rat_eq _ _ hh1] at hb
  exact hb

theorem dilationGrid_core_nat_rat_cancel {k h ell : ℕ}
    (hh : h ∈ Finset.Icc 1 k) (hell : ell ≤ k) (g : ℕ → ℚ) :
    (∑ e : DilationGridVertex k, dilationCubeWeight (k + 1) e *
      ((dilationGridMultiplier k e : ℚ) ^ ell * g (dilationGridShift k e h))) = 0 := by
  have hb := dilationGrid_core_rat_cancel hh hell (fun z => g z.num.natAbs)
  simpa only [Rat.num_natCast, Int.natAbs_natCast] using hb

/-- Rational indicator tests suffice to cancel arbitrary real functions of a
finite family of shifts. -/
theorem rational_shift_cancellation_real {ι : Type*} [Fintype ι]
    (s : ι → ℕ) (a : ι → ℚ)
    (hcancel : ∀ g : ℕ → ℚ, (∑ i, a i * g (s i)) = 0) (g : ℕ → ℝ) :
    (∑ i, (a i : ℝ) * g (s i)) = 0 := by
  classical
  have hreal (u : ℕ) : (∑ i, if s i = u then (a i : ℝ) else 0) = 0 := by
    have hh := hcancel (fun x => if x = u then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at hh
    simp only [← Finset.sum_filter] at hh ⊢
    exact_mod_cast hh
  calc
    _ = ∑ i, ∑ u ∈ Finset.univ.image s,
        if s i = u then (a i : ℝ) * g u else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Finset.mem_image_of_mem s (Finset.mem_univ i)]
    _ = ∑ u ∈ Finset.univ.image s,
        (∑ i, if s i = u then (a i : ℝ) else 0) * g u := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul, ite_mul, zero_mul]
    _ = 0 := by simp only [hreal, zero_mul, Finset.sum_const_zero]

/-- Actual integer weights cancel every real-valued shifted core through degree `k`. -/
theorem dilationGrid_core_cancel {k h ell : ℕ}
    (hh : h ∈ Finset.Icc 1 k) (hell : ell ≤ k) (g : ℕ → ℝ) :
    (∑ e : DilationGridVertex k, (dilationGridWeightInt k e : ℝ) *
      ((dilationGridMultiplier k e : ℝ) ^ ell * g (dilationGridShift k e h))) = 0 := by
  have hb := rational_shift_cancellation_real (fun e : DilationGridVertex k => dilationGridShift k e h)
    (fun e => dilationCubeWeight (k + 1) e * (dilationGridMultiplier k e : ℚ) ^ ell)
    (fun f => by simpa only [mul_assoc] using dilationGrid_core_nat_rat_cancel hh hell f) g
  simp_rw [← dilationGridWeightInt_rat] at hb
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_intCast, mul_assoc] using hb

/-- In particular, the actual divisor-power terms of every exponent cancel. -/
theorem dilationGrid_sigma_core_cancel (N : ℕ) {k h ell : ℕ}
    (hh : h ∈ Finset.Icc 1 k) (hell : ell ≤ k) :
    (∑ e : DilationGridVertex k, (dilationGridWeightInt k e : ℝ) *
      ((dilationGridMultiplier k e : ℝ) ^ ell *
        ((ArithmeticFunction.sigma k (N + dilationGridShift k e h) : ℝ) /
          ((N + dilationGridShift k e h : ℕ) : ℝ) ^ ell))) = 0 :=
  dilationGrid_core_cancel hh hell
    (fun s => (ArithmeticFunction.sigma k (N + s) : ℝ) / ((N + s : ℕ) : ℝ) ^ ell)

#print axioms dilationGridWeightInt_rat
#print axioms dilationGridWeightInt_zero_ne_zero
#print axioms dilationGridMultiplier_rat_eq_cube
#print axioms dilationGridOffset_rat_eq_cube
#print axioms dilationGridShift_rat_eq
#print axioms dilationGrid_core_rat_cancel
#print axioms dilationGrid_core_nat_rat_cancel
#print axioms rational_shift_cancellation_real
#print axioms dilationGrid_core_cancel
#print axioms dilationGrid_sigma_core_cancel

end Erdos252
