import Generalizations.Cantor
import Mathlib.Data.Nat.Totient

/-!
# Explicit numerator and denominator families

The results here do not require multiplicativity. Bounds by a divisor sum
allow arbitrary signed integer perturbations and arbitrary sufficiently large
integer bases. The factorial-power family covers every natural divisor-sum index.
-/

namespace Erdos252.Generalizations

open Filter
open scoped BigOperators Topology ArithmeticFunction.sigma

noncomputable section

theorem tendsto_sigma_ratio (k : ℕ) :
    Tendsto (fun n : ℕ => (σ k (n + 2) : ℝ) / ((n + 2 : ℕ) : ℝ) ^ (k + 1))
      atTop (𝓝 0) := by
  simpa only [Erdos252.phase, pow_succ, div_div, Function.comp_def] using
    (Erdos252.tendsto_phase_div_nat k).comp (tendsto_add_atTop_nat 2)

theorem bases_ge_two {k : ℕ} {q : ℕ → ℕ}
    (hq : ∀ n, (n + 2) ^ (k + 1) ≤ q n) (n : ℕ) : 2 ≤ q n := by
  have hp : 1 ≤ (n + 2) ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have := hq n
  rw [pow_succ] at this
  nlinarith

/-- Any signed integer numerator bounded by `C * sigma k (n+2)` works with
any product bases at least `(n+2)^(k+1)`. No multiplicativity is assumed. -/
theorem irrational_of_sigma_bound {a : ℕ → ℤ} {q : ℕ → ℕ} (k : ℕ)
    (hq : ∀ n, (n + 2) ^ (k + 1) ≤ q n) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, ‖(a n : ℝ)‖ ≤ C * (σ k (n + 2) : ℝ))
    (hne : ¬ ∀ᶠ n in atTop, a n = 0) : Irrational (cantorSum a q) := by
  apply irrational_cantor (bases_ge_two hq) _ hne
  apply squeeze_zero_norm
    (a := fun n => C * ((σ k (n + 2) : ℝ) / ((n + 2 : ℕ) : ℝ) ^ (k + 1)))
  · intro n
    rw [norm_div, Real.norm_natCast, ← mul_div_assoc]
    exact (div_le_div_of_nonneg_right (ha n) (Nat.cast_nonneg _)).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast hq n))
  · simpa using (tendsto_sigma_ratio k).const_mul C

/-- Every divisor-power sum admits an entire class of product denominators. -/
theorem irrational_sigma_product (k : ℕ) (q : ℕ → ℕ)
    (hq : ∀ n, (n + 2) ^ (k + 1) ≤ q n) :
    Irrational (∑' n : ℕ, (σ k (n + 2) : ℝ) / denom q (n + 1)) := by
  apply irrational_of_sigma_bound (a := fun n => (σ k (n + 2) : ℤ)) k hq 1
    (by norm_num) (by intro n; simp) _
  intro hz
  obtain ⟨n, hn⟩ := hz.exists
  have hp := ArithmeticFunction.sigma_pos k (n + 2) (by omega)
  norm_cast at hn
  omega

theorem denom_factorial_pow (r n : ℕ) :
    denom (fun i => (i + 2) ^ r) n = (n + 1).factorial ^ r := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [denom_succ, ih, Nat.factorial_succ, Nat.mul_pow]
    ring

/-- Irrationality for the genuinely faster denominator `(n!)^(k+1)`. -/
theorem irrational_sigma_factorial_power (k : ℕ) :
    Irrational (∑' n : ℕ, (σ k n : ℝ) / (n.factorial : ℝ) ^ (k + 1)) := by
  have htail := irrational_sigma_product k (fun n => (n + 2) ^ (k + 1)) (fun _ => le_rfl)
  simp only [denom_factorial_pow, Nat.cast_pow, Nat.add_assoc] at htail
  have hs : Summable (fun n : ℕ => (σ k n : ℝ) / (n.factorial : ℝ) ^ (k + 1)) := by
    apply (summable_nat_add_iff 2).mp
    have ht : Summable (fun n => cantorTerm (fun n => (σ k (n + 2) : ℤ))
        (fun n => (n + 2) ^ (k + 1)) n) := summable_cantor
        (bases_ge_two (k := k) (q := fun n => (n + 2) ^ (k + 1)) (fun _ => le_rfl))
        (by simpa only [Int.cast_natCast, Nat.cast_pow] using tendsto_sigma_ratio k)
    simpa only [cantorTerm, denom_factorial_pow, Nat.cast_pow, Int.cast_natCast,
      Nat.add_assoc] using ht
  rw [← hs.sum_add_tsum_nat_add 2]
  simpa [Finset.sum_range_succ, ArithmeticFunction.sigma_one, add_comm] using htail.add_natCast 1

/-- A non-factorial denominator: products of quadratic values. -/
theorem irrational_sigma_quadratic_product :
    Irrational (∑' n : ℕ, (σ 1 (n + 2) : ℝ) /
      (∏ i ∈ Finset.range (n + 1), ((i + 2) ^ 2 + 1) : ℕ)) := by
  exact irrational_sigma_product 1 (fun n => (n + 2) ^ 2 + 1) (fun _ => by
    norm_num only [Nat.reduceAdd]
    omega)

/-- Alternating coefficients are allowed; positivity is not needed. -/
theorem irrational_alternating_sigma (k : ℕ) :
    Irrational (∑' n : ℕ, (-1 : ℝ) ^ n * (σ k (n + 2) : ℝ) /
      ((n + 2).factorial : ℝ) ^ (k + 1)) := by
  have h := irrational_of_sigma_bound
    (a := fun n => (-1 : ℤ) ^ n * (σ k (n + 2) : ℤ))
    (q := fun n => (n + 2) ^ (k + 1)) k (fun _ => le_rfl) 1 (by norm_num)
    (by intro n; simp [norm_mul, norm_pow]) (by
      intro hz
      obtain ⟨n, hn⟩ := hz.exists
      exact mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Int.natCast_ne_zero.mpr (ArithmeticFunction.sigma_pos k (n + 2) (by omega)).ne') hn)
  simpa only [cantorSum, cantorTerm, denom_factorial_pow, Nat.cast_pow, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, Nat.add_assoc] using h

end

end Erdos252.Generalizations
