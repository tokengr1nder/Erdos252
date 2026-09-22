import Generalizations.Joint

/-!
# Further examples and preservation of the original hard factorial case
-/

namespace Erdos252.Generalizations

open Filter
open scoped BigOperators Topology ArithmeticFunction.sigma

noncomputable section

theorem self_le_sigma_one (n : ℕ) (hn : n ≠ 0) : n ≤ σ 1 n := by
  simp only [ArithmeticFunction.sigma_apply, pow_one]
  exact Finset.single_le_sum (fun d (_ : d ∈ n.divisors) => Nat.zero_le d)
    (by simp [Nat.mem_divisors, hn] : n ∈ n.divisors)

/-- A different arithmetic numerator and a different factorial denominator. -/
theorem irrational_totient_factorial_squared :
    Irrational (∑' n : ℕ, ((n + 2).totient : ℝ) / ((n + 2).factorial : ℝ) ^ 2) := by
  have h := irrational_of_sigma_bound (a := fun n => ((n + 2).totient : ℤ))
    (q := fun n => (n + 2) ^ 2) 1 (fun _ => le_rfl) 1 (by norm_num) (by
      intro n
      simp only [Int.cast_natCast, Real.norm_natCast, one_mul]
      exact_mod_cast (Nat.totient_le (n + 2)).trans (self_le_sigma_one _ (by omega))) (by
      intro hz
      obtain ⟨n, hn⟩ := hz.exists
      have hp := Nat.totient_pos.mpr (by omega : 0 < n + 2)
      norm_cast at hn
      omega)
  simpa only [cantorSum, cantorTerm, denom_factorial_pow, Nat.cast_pow,
    Int.cast_natCast, Nat.add_assoc] using h

/-- Both sides change, and the numerator/base ratio oscillates rather than
tending to zero. Removing the alternating integer correction exposes sigma. -/
theorem irrational_oscillating_quadratic :
    Irrational (∑' n : ℕ,
      ((σ 1 (n + 2) : ℝ) + (-1 : ℝ) ^ n * (((n + 2 : ℕ) : ℝ) ^ 2 + 2)) /
        (∏ j ∈ Finset.range (n + 1), ((j + 2) ^ 2 + 1) : ℕ)) := by
  have h := irrational_corrected_sigma_product 1 (fun n => (n + 2) ^ 2 + 1)
    (fun n => by norm_num only [Nat.reduceAdd]; omega)
    (fun n => (-1 : ℤ) ^ n) 1 (by norm_num) (by intro n; simp [norm_pow])
  convert h using 1
  apply tsum_congr
  intro n
  push_cast
  rw [pow_succ]
  ring

theorem denom_factorial (n : ℕ) : denom (fun n => n + 2) n = (n + 1).factorial := by
  simpa only [pow_one] using denom_factorial_pow 1 n

theorem irrational_sigma_tail (k : ℕ) :
    Irrational (∑' n : ℕ, (σ k (n + 2) : ℝ) / ((n + 2).factorial : ℝ)) := by
  have h := Erdos252.erdos_252 k
  rw [← (summable_sigma_factorial k).sum_add_tsum_nat_add 2] at h
  have hp : (∑ i ∈ Finset.range 2, (σ k i : ℝ) / (i.factorial : ℝ)) = 1 := by
    simp [Finset.sum_range_succ, ArithmeticFunction.sigma_one]
  rw [hp] at h
  exact Irrational.of_natCast_add 1 (by simpa using h)

/-- The original all-degree result is preserved under arbitrary bounded integer
telescoping perturbations; the new numerator need not be multiplicative. -/
theorem irrational_corrected_sigma_factorial (k : ℕ) (b : ℕ → ℤ)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ n, ‖(b n : ℝ)‖ ≤ B) :
    Irrational (∑' n : ℕ,
      ((σ k (n + 2) : ℝ) + ((n + 2 : ℕ) : ℝ) * (b n : ℝ) - (b (n + 1) : ℝ)) /
        ((n + 2).factorial : ℝ)) := by
  let a : ℕ → ℤ := fun n => (σ k (n + 2) : ℤ) + (n + 2 : ℕ) * b n - b (n + 1)
  have hq (n : ℕ) : 2 ≤ n + 2 := by omega
  have hr : residual a b (fun n => n + 2) = fun n => (σ k (n + 2) : ℤ) := by
    funext n
    dsimp [residual, a]
    ring
  have hsigma : Summable (cantorTerm (fun n => (σ k (n + 2) : ℤ)) (fun n => n + 2)) := by
    change Summable (fun n => (σ k (n + 2) : ℝ) / denom (fun n => n + 2) (n + 1))
    simpa only [denom_factorial, Nat.add_assoc] using
      (summable_nat_add_iff 2).mpr (summable_sigma_factorial k)
  have hs := hasSum_normalized hq a b (summable_bounded_correction hq b B hB hb)
    (by rw [hr]; exact hsigma)
  have hirr := (irrational_sigma_tail k).intCast_add (b 0)
  have hid : cantorSum (fun n => (σ k (n + 2) : ℤ)) (fun n => n + 2) =
      ∑' n : ℕ, (σ k (n + 2) : ℝ) / ((n + 2).factorial : ℝ) := by
    simp only [cantorSum, cantorTerm, denom_factorial, Nat.add_assoc, Int.cast_natCast]
  rw [← hid, ← hr, ← hs.tsum_eq] at hirr
  simpa only [cantorTerm, a, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    denom_factorial, Nat.add_assoc] using hirr

end

end Erdos252.Generalizations
