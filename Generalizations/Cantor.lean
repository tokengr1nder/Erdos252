import Erdos252.Solution

/-!
# Integer coefficients and arbitrary product denominators

The numerator need not be multiplicative, positive, or a divisor sum.
The denominator is a product of integer bases, not necessarily a factorial.
This is a formalisation of a classical small-coefficient Cantor-series criterion;
it is not claimed as a new irrationality criterion.
-/

namespace Erdos252.Generalizations

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The empty product is one; the `n`th term has denominator `denom q (n+1)`. -/
def denom (q : ℕ → ℕ) (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, q i

@[simp] theorem denom_zero (q : ℕ → ℕ) : denom q 0 = 1 := by simp [denom]

theorem denom_succ (q : ℕ → ℕ) (n : ℕ) :
    denom q (n + 1) = denom q n * q n := by simp [denom, Finset.prod_range_succ]

theorem denom_pos {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n) (n : ℕ) : 0 < denom q n :=
  Finset.prod_pos fun i _ => lt_of_lt_of_le (by decide) (hq i)

theorem denom_growth {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n) (n j : ℕ) :
    denom q n * 2 ^ j ≤ denom q (n + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    change denom q n * 2 ^ (j + 1) ≤ denom q ((n + j) + 1)
    rw [denom_succ, pow_succ, ← mul_assoc]
    exact Nat.mul_le_mul ih (hq _)

theorem denom_dvd {q : ℕ → ℕ} {i n : ℕ} (h : i ≤ n) : denom q i ∣ denom q n := by
  induction n, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ n h ih => exact ih.trans (by rw [denom_succ]; exact dvd_mul_right _ _)

def cantorTerm (a : ℕ → ℤ) (q : ℕ → ℕ) (n : ℕ) : ℝ :=
  (a n : ℝ) / denom q (n + 1)

def cantorSum (a : ℕ → ℤ) (q : ℕ → ℕ) : ℝ := ∑' n, cantorTerm a q n

def cantorTail (a : ℕ → ℤ) (q : ℕ → ℕ) (n : ℕ) : ℝ :=
  (denom q n : ℝ) * (cantorSum a q - ∑ i ∈ Finset.range n, cantorTerm a q i)

/-- The denominator products control every shifted, scaled summand. -/
theorem scaled_term_bound {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n)
    (a : ℕ → ℤ) (n j : ℕ) :
    ‖(denom q n : ℝ) * cantorTerm a q (n + j)‖ ≤
      ‖(a (n + j) : ℝ) / q (n + j)‖ * (1 / 2 : ℝ) ^ j := by
  have hD : (0 : ℝ) < denom q (n + j) := Nat.cast_pos.mpr (denom_pos hq _)
  have hratio : (denom q n : ℝ) / denom q (n + j) ≤ (1 / 2 : ℝ) ^ j := by
    rw [div_pow, one_pow, div_le_div_iff₀ hD (by positivity)]
    simpa using (show (denom q n : ℝ) * (2 : ℝ) ^ j ≤ denom q (n + j) from
      by exact_mod_cast denom_growth hq n j)
  have heq : (denom q n : ℝ) * cantorTerm a q (n + j) =
      ((a (n + j) : ℝ) / q (n + j)) *
        ((denom q n : ℝ) / denom q (n + j)) := by
    simp only [cantorTerm, denom_succ, Nat.cast_mul]
    ring
  rw [heq, norm_mul, Real.norm_of_nonneg
    (show 0 ≤ (denom q n : ℝ) / denom q (n + j) by positivity)]
  exact mul_le_mul_of_nonneg_left hratio (norm_nonneg _)

theorem summable_cantor {a : ℕ → ℤ} {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n)
    (ha : Tendsto (fun n => (a n : ℝ) / q n) atTop (𝓝 0)) :
    Summable (cantorTerm a q) := by
  obtain ⟨C, hC⟩ := ha.norm.bddAbove_range
  refine ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left C).of_norm_bounded fun n => ?_
  have h := scaled_term_bound hq a 0 n
  simp only [denom_zero, Nat.cast_one, one_mul, zero_add] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hC (Set.mem_range_self n)) (by positivity))

/-- Every scaled tail tends to zero, including for signed coefficients. -/
theorem tendsto_cantorTail {a : ℕ → ℤ} {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n)
    (ha : Tendsto (fun n => (a n : ℝ) / q n) atTop (𝓝 0)) :
    Tendsto (cantorTail a q) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := ha.norm.bddAbove_range
  have hs := summable_cantor hq ha
  have ht (j : ℕ) : Tendsto (fun n => (denom q n : ℝ) * cantorTerm a q (n + j))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (scaled_term_bound hq a · j)
    simpa using (ha.norm.comp (tendsto_add_atTop_nat j)).mul_const ((1 / 2 : ℝ) ^ j)
  have hg := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left C
  have hlim := tendsto_tsum_of_dominated_convergence hg ht
    (Eventually.of_forall fun n j => (scaled_term_bound hq a n j).trans
      (mul_le_mul_of_nonneg_right (hC (Set.mem_range_self (n + j))) (by positivity)))
  simp only [tsum_zero] at hlim
  convert hlim using 1
  ext n
  rw [cantorTail, cantorSum, ← hs.sum_add_tsum_nat_add n, add_sub_cancel_left,
    ← tsum_mul_left]
  exact tsum_congr fun j => by rw [Nat.add_comm j n]

theorem cantor_prefix_integral {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n)
    (a : ℕ → ℤ) (n : ℕ) :
    ∃ z : ℤ, (denom q n : ℝ) * (∑ i ∈ Finset.range n, cantorTerm a q i) = z := by
  refine ⟨∑ i ∈ Finset.range n, (denom q n / denom q (i + 1) : ℕ) * a i, ?_⟩
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.mul_sum, cantorTerm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.cast_div (denom_dvd (q := q) (i := i + 1) (n := n)
    (by have := Finset.mem_range.mp hi; omega))
    (Nat.cast_ne_zero.mpr (denom_pos hq (i + 1)).ne')]
  ring

theorem cantorTail_step {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n)
    (a : ℕ → ℤ) (n : ℕ) :
    (q n : ℝ) * cantorTail a q n = (a n : ℝ) + cantorTail a q (n + 1) := by
  have hD : (denom q n : ℝ) ≠ 0 := (Nat.cast_pos.mpr (denom_pos hq n)).ne'
  have hq0 : (q n : ℝ) ≠ 0 := (Nat.cast_pos.mpr (by have := hq n; omega)).ne'
  simp only [cantorTail, Finset.sum_range_succ, cantorTerm, denom_succ, Nat.cast_mul]
  field_simp
  ring

/-- Rationality forces the coefficients eventually to vanish. No denominator
divisibility hypothesis beyond the product form is required. -/
theorem eventually_zero_of_rational_cantor {a : ℕ → ℤ} {q : ℕ → ℕ}
    (hq : ∀ n, 2 ≤ q n) (ha : Tendsto (fun n => (a n : ℝ) / q n) atTop (𝓝 0))
    (hr : ¬ Irrational (cantorSum a q)) : ∀ᶠ n in atTop, a n = 0 := by
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hr
  have hint (n : ℕ) : ∃ z : ℤ, (r.den : ℝ) * cantorTail a q n = z := by
    obtain ⟨z, hz⟩ := cantor_prefix_integral hq a n
    refine ⟨(denom q n : ℤ) * r.num - (r.den : ℤ) * z, ?_⟩
    push_cast
    have hrden : (r.den : ℝ) * (r : ℝ) = r.num := by
      rw [Rat.cast_def]
      field_simp
    calc
      _ = (denom q n : ℝ) * ((r.den : ℝ) * (r : ℝ)) -
          (r.den : ℝ) * ((denom q n : ℝ) *
            ∑ i ∈ Finset.range n, cantorTerm a q i) := by rw [cantorTail, hr]; ring
      _ = _ := by rw [hrden, hz]
  have hz := Erdos252.eventually_zero_of_int
    (by simpa using (tendsto_cantorTail hq ha).const_mul (r.den : ℝ))
    (Eventually.of_forall hint)
  have ht : ∀ᶠ n in atTop, cantorTail a q n = 0 := hz.mono fun n hn =>
    (mul_eq_zero.mp hn).resolve_left (by exact_mod_cast r.den_nz)
  filter_upwards [ht, (tendsto_add_atTop_nat 1).eventually ht] with n hn hn1
  have heq := cantorTail_step hq a n
  rw [hn, hn1, mul_zero, add_zero] at heq
  exact_mod_cast heq.symm

/-- A general numerator/denominator theorem: signed integer coefficients,
arbitrary integer bases at least two, and a vanishing coefficient/base ratio. -/
theorem irrational_cantor {a : ℕ → ℤ} {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n)
    (ha : Tendsto (fun n => (a n : ℝ) / q n) atTop (𝓝 0))
    (hne : ¬ ∀ᶠ n in atTop, a n = 0) : Irrational (cantorSum a q) := by
  by_contra h
  exact hne (eventually_zero_of_rational_cantor hq ha h)

/-- Within the small-coefficient class, the criterion is an equivalence. -/
theorem irrational_cantor_iff {a : ℕ → ℤ} {q : ℕ → ℕ} (hq : ∀ n, 2 ≤ q n)
    (ha : Tendsto (fun n => (a n : ℝ) / q n) atTop (𝓝 0)) :
    Irrational (cantorSum a q) ↔ ¬ ∀ᶠ n in atTop, a n = 0 := by
  refine ⟨fun hi hz => ?_, irrational_cantor hq ha⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hz
  have ht : (∑' n, cantorTerm a q (n + N)) = 0 := by
    calc
      _ = ∑' _n : ℕ, (0 : ℝ) := tsum_congr fun n => by
        simp [cantorTerm, hN (n + N) (by omega)]
      _ = 0 := tsum_zero
  rw [cantorSum, ← (summable_cantor hq ha).sum_add_tsum_nat_add N, ht, add_zero] at hi
  have heq : ((∑ i ∈ Finset.range N, (a i : ℚ) / denom q (i + 1) : ℚ) : ℝ) =
      ∑ i ∈ Finset.range N, cantorTerm a q i := by
    push_cast
    rfl
  rw [← heq] at hi
  exact (∑ i ∈ Finset.range N, (a i : ℚ) / denom q (i + 1) : ℚ).not_irrational hi

end

end Erdos252.Generalizations
