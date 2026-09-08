import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary support for arithmetic-progression means

These periodic-average and prime-gcd lemmas are independent of any divisor-sum
exponent. Their existing names are retained so the historical APIs re-export
the same declarations.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The floor quotient has the expected normalized limit. -/
theorem nat_div_ratio_tendsto5 {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / (N : ℝ)) atTop
      (𝓝 (1 / (d : ℝ))) := by
  simpa only [Function.comp_def, one_div_mul_eq_div, Nat.floor_div_eq_div] using
    (tendsto_nat_floor_mul_div_atTop (a := (1 : ℝ) / (d : ℝ))
      (div_pos zero_lt_one (Nat.cast_pos.mpr hd)).le).comp tendsto_natCast_atTop_atTop

/-- Complete blocks of a periodic sequence have their exact expected sum. -/
theorem periodic_sum_blocks5 {f : ℕ → ℝ} {d : ℕ}
    (hf : Function.Periodic f d) (b : ℕ) :
    (∑ n ∈ Finset.range (d * b), f n) =
      (b : ℝ) * ∑ n ∈ Finset.range d, f n := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have hp (n : ℕ) : f (d * b + n) = f n := by
        simpa only [Nat.cast_id, Nat.mul_comm, Nat.add_comm] using (hf.nat_mul b) n
      simp_rw [hp]
      push_cast
      ring

/-- Every nonnegative periodic sequence has its one-period Cesàro mean. -/
theorem periodic_nonneg_cesaro5 {f : ℕ → ℝ} {d : ℕ}
    (hd : 0 < d) (hf : Function.Periodic f d) (hpos : ∀ n, 0 ≤ f n) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f n) / (N : ℝ)) atTop
      (𝓝 ((∑ n ∈ Finset.range d, f n) / (d : ℝ))) := by
  let S := ∑ n ∈ Finset.range d, f n
  have hlo : Tendsto (fun N : ℕ => (((N / d : ℕ) : ℝ) / (N : ℝ)) * S) atTop
      (𝓝 (S / (d : ℝ))) := by
    simpa only [one_div_mul_eq_div] using (nat_div_ratio_tendsto5 hd).mul_const S
  have hhi : Tendsto (fun N : ℕ =>
      (((N / d : ℕ) : ℝ) / (N : ℝ) + 1 / (N : ℝ)) * S) atTop
      (𝓝 (S / (d : ℝ))) := by
    simpa only [add_zero, one_div_mul_eq_div] using
      ((nat_div_ratio_tendsto5 hd).add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).mul_const S
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro N
    have hcover := Nat.mul_div_le N d
    have hh := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hcover)
      (fun n _ _ => hpos n)
    rw [periodic_sum_blocks5 hf] at hh
    have hr := div_le_div_of_nonneg_right hh (by positivity : (0 : ℝ) ≤ N)
    convert hr using 1; first | rfl | ring
  · intro N
    have hcover := (Nat.lt_mul_div_succ N hd).le
    have hh := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hcover)
      (fun n _ _ => hpos n)
    rw [periodic_sum_blocks5 hf] at hh
    have hr := div_le_div_of_nonneg_right hh (by positivity : (0 : ℝ) ≤ N)
    convert hr using 1; first | rfl | (push_cast; ring)

/-- The prime's local gcd is either the prime or one. -/
theorem rawPhaseFreshPrime_gcd {ell : ℕ} (hp : ell.Prime) (d : ℕ) :
    Nat.gcd d ell = if ell ∣ d then ell else 1 := by
  by_cases h : ell ∣ d
  · simp [h, Nat.gcd_eq_right h]
  · simpa [h] using (hp.coprime_iff_not_dvd.mpr h).symm.gcd_eq_one

#print axioms nat_div_ratio_tendsto5
#print axioms periodic_sum_blocks5
#print axioms periodic_nonneg_cesaro5
#print axioms rawPhaseFreshPrime_gcd

end

end Erdos252
