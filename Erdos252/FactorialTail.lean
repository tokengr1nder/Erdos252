import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Real.Irrational

/-!
# Elementary prerequisites and the factorial tail

Rationality forces late factorial multiples to be integers, the divisor-sum
factorial series converges, an eventually integral null sequence is eventually
zero, and divisor pairing bounds the divisor sum by a square root. On that
basis the reciprocal descending product gets a Stirling expansion of any
order with a nonnegative error, which splits the scaled `alpha k` tail into a
finite main term and an exact error that is `o(1/n)`.
-/

namespace Erdos252

open Filter
open scoped Nat BigOperators Topology ArithmeticFunction.sigma

/-- If a real number is rational, then all sufficiently late factorial
multiples of it are integers. -/
theorem factorial_mul_eventually_int {x : ℝ} (hx : ¬ Irrational x) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ z : ℤ, (n.factorial : ℝ) * x = z := by
  obtain ⟨r, rfl⟩ := exists_rat_of_not_irrational hx
  refine ⟨r.den, fun n hn ↦ ?_⟩
  obtain ⟨c, hc⟩ := Nat.dvd_factorial r.pos hn
  refine ⟨(c : ℤ) * r.num, ?_⟩
  rw [Rat.cast_def, hc]
  push_cast
  field_simp

/-- Every fixed polynomial divided by `n!` is summable. -/
theorem summable_natPow_div_factorial (d : ℕ) : Summable (fun n : ℕ ↦ (n : ℝ) ^ d / (n ! : ℝ)) := by
  refine .of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
    (Real.summable_pow_div_factorial ((2 : ℝ) ^ d))
  gcongr
  exact_mod_cast (by simpa only [← pow_mul, Nat.mul_comm] using
    Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := n)).le d : n ^ d ≤ (2 ^ d) ^ n)

/-- The Erdős 252 factorial series is summable for every exponent `k`. -/
theorem summable_sigma_factorial (k : ℕ) : Summable (fun n : ℕ ↦ (σ k n : ℝ) / (n ! : ℝ)) := by
  refine .of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
    (summable_natPow_div_factorial (k + 1))
  gcongr
  exact_mod_cast ArithmeticFunction.sigma_le_pow_succ k n

theorem eventually_zero_of_int {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0))
    (hint : ∀ᶠ n in atTop, ∃ z : ℤ, f n = z) :
    ∀ᶠ n in atTop, f n = 0 := by
  filter_upwards [hint, ((tendsto_zero_iff_abs_tendsto_zero _).mp hf).eventually
    (gt_mem_nhds one_pos)] with n ⟨z, hz⟩ hs
  rw [Function.comp_apply, hz] at hs
  rw [hz]
  exact_mod_cast Int.abs_lt_one_iff.mp (by exact_mod_cast hs)

private theorem card_divisors_le_sqrt (n : ℕ) (hn : 0 < n) : n.divisors.card ≤ 2 * Nat.sqrt n := by
  let S := Finset.Icc 1 (Nat.sqrt n)
  have hcover : n.divisors ⊆ S ∪ S.image (fun d => n / d) := by
    intro d hd
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hdpos := Nat.pos_of_dvd_of_pos hdvd hn
    rcases Nat.le_sqrt_of_eq_mul (Nat.mul_div_cancel' hdvd).symm with hsmall | hsmall
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hdpos, hsmall⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨n / d,
        Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn hdvd) hdpos, hsmall⟩,
        Nat.div_div_self hdvd hn.ne'⟩
  calc
    _ ≤ (S ∪ S.image (fun d => n / d)).card := Finset.card_le_card hcover
    _ ≤ S.card + (S.image (fun d => n / d)).card := Finset.card_union_le _ _
    _ ≤ S.card + S.card := Nat.add_le_add_left (Finset.card_image_le) _
    _ = _ := by simp [S, two_mul]

/-- Bounding every divisor by `n` and their number by a square root. -/
theorem sigma_le_pow_sqrt (k n : ℕ) (hn : 0 < n) : (σ k n : ℝ) ≤ 64 * (n : ℝ) ^ k * √(n : ℝ) := by
  have hnat : σ k n ≤ n.divisors.card * n ^ k := by
    simpa only [ArithmeticFunction.sigma_apply, Finset.sum_const, nsmul_eq_mul, Nat.cast_id] using
      Finset.sum_le_sum (s := n.divisors)
        (fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) k)
  have hcard : (n.divisors.card : ℝ) ≤ 64 * √(n : ℝ) := by
    calc
      _ ≤ 2 * (Nat.sqrt n : ℝ) := by exact_mod_cast card_divisors_le_sqrt n hn
      _ ≤ 2 * √(n : ℝ) := mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)
  refine le_trans (b := (n.divisors.card : ℝ) * (n : ℝ) ^ k) (by exact_mod_cast hnat) ?_
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_right hcard (pow_nonneg (Nat.cast_nonneg n) k)

theorem sigma_div_le_sqrt (k n : ℕ) (hn : 0 < n) : (σ k n : ℝ) / (n : ℝ) ^ k ≤ 64 * √(n : ℝ) := by
  have hpow : (0 : ℝ) < (n : ℝ) ^ k := by positivity
  apply (div_le_iff₀ hpow).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using sigma_le_pow_sqrt k n hn

/-- The square-root growth majorant is still sublinear. -/
theorem tendsto_sqrt_div_nat :
    Tendsto (fun n : ℕ => √(n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  simpa only [Real.sqrt_div_self, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- The reciprocal product centered at its largest factor. -/
noncomputable def descRecip (h : ℕ) (x : ℝ) : ℝ := 1 / ∏ j ∈ Finset.range h, (x - (j : ℝ))

/-- The Stirling expansion of the `j+1` factor product through reciprocal degree `L`. -/
noncomputable def stirlingPoly (j L : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range L, (Nat.stirlingSecond i j : ℝ) / x ^ (i + 1)

/-- The exact remainder after the finite Stirling expansion. -/
noncomputable def stirlingErr (j L : ℕ) (x : ℝ) : ℝ := descRecip (j + 1) x - stirlingPoly j L x

theorem descRecip_succ (h : ℕ) (x : ℝ) : descRecip (h + 1) x = descRecip h x / (x - (h : ℝ)) := by
  simp only [descRecip, Finset.prod_range_succ, div_div]

theorem descRecip_one (x : ℝ) : descRecip 1 x = 1 / x := by
  simp [descRecip]

theorem stirlingPoly_zero (j : ℕ) (x : ℝ) : stirlingPoly j 0 x = 0 := by
  simp [stirlingPoly]

theorem stirlingPoly_one (L : ℕ) (x : ℝ) : stirlingPoly 0 (L + 1) x = 1 / x := by
  simp [stirlingPoly, Finset.sum_range_succ', Nat.stirlingSecond]

/-- The finite coefficient recurrence holds at every truncation order. -/
theorem stirlingPoly_recurrence (j L : ℕ) (x : ℝ) : stirlingPoly (j + 1) (L + 1) x =
      (stirlingPoly j L x + ((j : ℝ) + 1) * stirlingPoly (j + 1) L x) / x := by
  unfold stirlingPoly
  rw [Finset.sum_range_succ']
  simp only [Nat.stirlingSecond_zero_succ, Nat.cast_zero, zero_div, add_zero]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.stirlingSecond_succ_succ]
  push_cast
  simp only [pow_succ, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Consequently the exact errors obey a positive finite recurrence. -/
theorem stirlingErr_recurrence (j L : ℕ) (x : ℝ) (hx : x ≠ 0) (hxj : x - ((j : ℝ) + 1) ≠ 0) :
    stirlingErr (j + 1) (L + 1) x =
      (stirlingErr j L x + ((j : ℝ) + 1) * stirlingErr (j + 1) L x) / x := by
  have h : x * descRecip (j + 2) x = descRecip (j + 1) x + ((j : ℝ) + 1) * descRecip (j + 2) x := by
    rw [show j + 2 = (j + 1) + 1 from rfl, descRecip_succ]
    push_cast
    field_simp
    ring
  unfold stirlingErr
  rw [stirlingPoly_recurrence j L x]
  apply (eq_div_iff hx).mpr
  field_simp
  nlinarith

/-- A centered descending product is positive and its reciprocal is at most
`1/x` once all its factors other than `x` are at least one. -/
theorem descRecip_bounds (h H : ℕ) (x : ℝ) (hh : 1 ≤ h) (hH : h ≤ H) (hx : (H : ℝ) ≤ x) :
    0 < descRecip h x ∧ descRecip h x ≤ 1 / x := by
  induction h, hh using Nat.le_induction with
  | base =>
    rw [descRecip_one]
    exact ⟨one_div_pos.mpr (lt_of_lt_of_le one_pos ((Nat.one_le_cast.mpr hH).trans hx)), le_rfl⟩
  | succ h hh ih =>
    have hdiff : (1 : ℝ) ≤ x - h := by
      have := (Nat.cast_le (α := ℝ)).mpr hH
      push_cast at this
      linarith
    have hb := ih (by omega)
    rw [descRecip_succ]
    exact ⟨div_pos hb.1 (by linarith), (div_le_self hb.1.le hdiff).trans hb.2⟩

/-- The finite error bound is uniform over all product lengths `1..H`.
No convergence theorem or unproved asymptotic hypothesis is used. -/
theorem stirlingErr_bounds (H L : ℕ) (x : ℝ) (hx : (H : ℝ) ≤ x) (j : ℕ) (hH : j + 1 ≤ H) :
    0 ≤ stirlingErr j L x ∧ stirlingErr j L x ≤ (H : ℝ) ^ L / x ^ (L + 1) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by exact_mod_cast (show 0 < H by omega)) hx
  induction L generalizing j with
  | zero =>
    simp only [stirlingErr, stirlingPoly_zero, sub_zero, pow_zero, zero_add, pow_one]
    exact ⟨(descRecip_bounds (j + 1) H x j.succ_pos hH hx).1.le,
      (descRecip_bounds (j + 1) H x j.succ_pos hH hx).2⟩
  | succ L ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [stirlingErr, Nat.zero_add, descRecip_one, stirlingPoly_one, sub_self]
      exact ⟨le_rfl, by positivity⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have hdiff : 0 < x - ((j : ℝ) + 1) := by
      have hjR : (j : ℝ) + 2 ≤ H := by exact_mod_cast hH
      linarith
    have hprev := ih j (by omega)
    have hcurr := ih (j + 1) hH
    rw [stirlingErr_recurrence j L x hxpos.ne' hdiff.ne']
    refine ⟨div_nonneg (add_nonneg hprev.1 (mul_nonneg (by positivity) hcurr.1)) hxpos.le, ?_⟩
    calc
      _ ≤ ((H : ℝ) ^ L / x ^ (L + 1) + ((j : ℝ) + 1) * ((H : ℝ) ^ L / x ^ (L + 1))) / x :=
        (div_le_div_iff_of_pos_right hxpos).mpr
          (add_le_add hprev.2 (mul_le_mul_of_nonneg_left hcurr.2 (by positivity)))
      _ = ((j : ℝ) + 2) * (H : ℝ) ^ L / x ^ (L + 2) := by
        rw [pow_succ x (L + 1)]
        ring
      _ ≤ (H : ℝ) * (H : ℝ) ^ L / x ^ (L + 2) := by
        gcongr
        exact_mod_cast hH
      _ = (H : ℝ) ^ (L + 1) / x ^ (L + 1 + 1) := by ring

/-- The generic descending product is exactly the actual ascending-factorial
denominator when centered at its largest factor. -/
theorem descRecip_centered (n h : ℕ) :
    descRecip h ((n + h : ℕ) : ℝ) = 1 / ((n + 1).ascFactorial h : ℝ) := by
  unfold descRecip
  rw [Nat.ascFactorial_eq_prod_range]
  push_cast
  congr 1
  rw [← Finset.prod_range_reflect (fun j : ℕ => (n : ℝ) + (h : ℝ) - (j : ℝ)) h]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hjh := Finset.mem_range.mp hj
  push_cast [Nat.cast_sub (by omega : j ≤ h - 1), Nat.cast_sub (by omega : 1 ≤ h)]
  ring

/-- The factorial divisor-sum series.  Its `n = 0` term is zero. -/
noncomputable def alpha (k : ℕ) : ℝ := ∑' n : ℕ, (σ k n : ℝ) / (n ! : ℝ)

/-- The actual factorial-series prefix, excluding the term at `n`. -/
noncomputable def seriesPrefix (k n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, (σ k m : ℝ) / (m.factorial : ℝ)

/-- The actual factorial tail starting at `n`, scaled by `(n-1)!`. -/
noncomputable def scaledTail (k n : ℕ) : ℝ := ((n - 1).factorial : ℝ) * (alpha k - seriesPrefix k n)

/-- One actual ascending-factorial term in the scaled tail. -/
noncomputable def blockTerm (k n j : ℕ) : ℝ := (σ k (n + j) : ℝ) / (n.ascFactorial (j + 1) : ℝ)

/-- The generic finite Stirling expansion, in the `n!` indexing convention. -/
noncomputable def tailMain (k n : ℕ) : ℝ := ∑ j ∈ Finset.range (k + 1),
    (σ k (n + (j + 1)) : ℝ) * stirlingPoly j (k + 1) ((n + (j + 1) : ℕ) : ℝ)

/-- The exact error between the actual generic tail and its finite expansion. -/
noncomputable def tailErr (k n : ℕ) : ℝ := scaledTail k (n + 1) - tailMain k n

/-- The omitted actual tail after `H` ascending-factorial terms. -/
noncomputable def omittedTail (k n H : ℕ) : ℝ := ∑' r : ℕ, blockTerm k (n + 1) (r + H)

/-- The finite part of the actual expansion error. -/
noncomputable def finiteErr (k n : ℕ) : ℝ := ∑ j ∈ Finset.range (k + 1),
    (σ k (n + (j + 1)) : ℝ) * stirlingErr j (k + 1) ((n + (j + 1) : ℕ) : ℝ)

/-- The factorial-scaled actual prefix is integral for every exponent. -/
theorem seriesPrefix_integral (k n : ℕ) :
    ∃ z : ℤ, ((n - 1).factorial : ℝ) * seriesPrefix k n = z := by
  refine ⟨((∑ m ∈ Finset.range n, ((n - 1).factorial / m.factorial) * σ k m : ℕ) : ℤ), ?_⟩
  unfold seriesPrefix
  rw [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun m hm => ?_
  push_cast [Nat.factorial_dvd_factorial (Nat.le_sub_one_of_lt (Finset.mem_range.mp hm))]
  field

/-- Rationality makes every sufficiently late actual scaled tail integral. -/
theorem eventually_scaledTail_integral (k : ℕ) (hx : ¬ Irrational (alpha k)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ z : ℤ, scaledTail k n = z := by
  obtain ⟨N, hN⟩ := factorial_mul_eventually_int hx
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨za, hza⟩ := hN (n - 1) (by omega)
  obtain ⟨zp, hzp⟩ := seriesPrefix_integral k n
  exact ⟨za - zp, by rw [scaledTail, mul_sub, hza, hzp, Int.cast_sub]⟩

private theorem factorial_ratio (n j : ℕ) (hn : 0 < n) :
    ((n - 1).factorial : ℝ) / ((n + j).factorial : ℝ) = 1 / (n.ascFactorial (j + 1) : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have ha : ((m + 1).ascFactorial (j + 1) : ℝ) ≠ 0 := by positivity
  field_simp
  norm_cast
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.add_assoc, Nat.add_comm 1] using
    Nat.factorial_mul_ascFactorial m (j + 1)

private theorem scaled_summand_eq_blockTerm (k n j : ℕ) (hn : 0 < n) : ((n - 1).factorial : ℝ) *
        ((σ k (j + n) : ℝ) / ((j + n).factorial : ℝ)) =
      blockTerm k n j := by
  rw [Nat.add_comm j n]
  unfold blockTerm
  rw [mul_div_left_comm, factorial_ratio n j hn, mul_one_div]

theorem scaledTail_tsum (k n : ℕ) (hn : 0 < n) : scaledTail k n = ∑' j : ℕ, blockTerm k n j := by
  unfold scaledTail alpha seriesPrefix
  rw [← (summable_sigma_factorial k).sum_add_tsum_nat_add n, add_sub_cancel_left, ← tsum_mul_left]
  exact tsum_congr (fun j => scaled_summand_eq_blockTerm k n j hn)

theorem summable_blockTerm (k n : ℕ) (hn : 0 < n) : Summable (blockTerm k n) :=
  (((summable_nat_add_iff n).2 (summable_sigma_factorial k)).mul_left
    ((n - 1).factorial : ℝ)).congr (fun j => scaled_summand_eq_blockTerm k n j hn)

theorem blockTerm_nonneg (k n j : ℕ) : 0 ≤ blockTerm k n j := by
  unfold blockTerm
  positivity

theorem omittedTail_nonneg (k n H : ℕ) : 0 ≤ omittedTail k n H :=
  tsum_nonneg (fun r => blockTerm_nonneg k (n + 1) (r + H))

/-- Splitting the actual tail at any finite order. -/
theorem scaledTail_split (k n H : ℕ) :
    scaledTail k (n + 1) = (∑ j ∈ Finset.range H, blockTerm k (n + 1) j) + omittedTail k n H := by
  rw [scaledTail_tsum k (n + 1) (by omega)]
  exact ((summable_blockTerm k (n + 1) (by omega)).sum_add_tsum_nat_add H).symm

/-- Each actual block summand has exactly the generic denominator error. -/
theorem blockTerm_expansion (k n j L : ℕ) : blockTerm k (n + 1) j =
      (σ k (n + (j + 1)) : ℝ) * stirlingPoly j L ((n + (j + 1) : ℕ) : ℝ) +
      (σ k (n + (j + 1)) : ℝ) * stirlingErr j L ((n + (j + 1) : ℕ) : ℝ) := by
  unfold blockTerm stirlingErr
  rw [descRecip_centered, Nat.add_right_comm n 1 j]
  ring_nf

/-- Exact decomposition of the generic actual expansion error into the
omitted infinite tail and the finite denominator remainders. -/
theorem tailErr_eq (k n : ℕ) : tailErr k n = omittedTail k n (k + 1) + finiteErr k n := by
  unfold tailErr tailMain finiteErr
  rw [scaledTail_split k n (k + 1)]
  simp_rw [blockTerm_expansion k n _ (k + 1)]
  rw [Finset.sum_add_distrib]
  ring

theorem scaledTail_expansion (k n : ℕ) : scaledTail k (n + 1) = tailMain k n + tailErr k n := by
  unfold tailErr
  ring

theorem tailErr_nonneg (k n : ℕ) (hn : k + 1 ≤ n) : 0 ≤ tailErr k n := by
  rw [tailErr_eq]
  refine add_nonneg (omittedTail_nonneg k n (k + 1))
    (Finset.sum_nonneg (fun j hj => mul_nonneg (Nat.cast_nonneg _) ?_))
  exact (stirlingErr_bounds (k + 1) (k + 1) ((n + (j + 1) : ℕ) : ℝ)
    (by exact_mod_cast (show k + 1 ≤ n + (j + 1) by omega)) j
    (by have := Finset.mem_range.mp hj; omega)).1

/-- The finite main term with both indices in the zero-based convention. -/
theorem tailMain_eq_range (k n : ℕ) : tailMain k n =
      ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1), (Nat.stirlingSecond i j : ℝ) *
          (σ k (n + (j + 1)) : ℝ) / ((n + (j + 1) : ℕ) : ℝ) ^ (i + 1) := by
  unfold tailMain stirlingPoly
  simp_rw [Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]

theorem poly_ascending_bound (d n r : ℕ) (hd : 0 < d) :
    (n + 1 + (r + d)) ^ d * (n + 1) ^ (r + 1) ≤ d ^ d * (n + 1).ascFactorial (r + d + 1) := by
  have hlin : n + 1 + (r + d) ≤ d * (n + 1 + (r + 1)) := by
    have hh : 0 ≤ (d - 1) * (n + r + 1) := Nat.zero_le _
    have hdd : d - 1 + 1 = d := by omega
    nlinarith
  have hnum : (n + 1 + (r + d)) ^ d ≤ d ^ d * (n + 1 + (r + 1)).ascFactorial d := by
    calc
      _ ≤ (d * (n + 1 + (r + 1))) ^ d := Nat.pow_le_pow_left hlin d
      _ = d ^ d * (n + 1 + (r + 1)) ^ d := Nat.mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_succ_le_ascFactorial _ _)
  calc
    _ ≤ (d ^ d * (n + 1 + (r + 1)).ascFactorial d) * (n + 1).ascFactorial (r + 1) :=
      Nat.mul_le_mul hnum (Nat.pow_succ_le_ascFactorial _ _)
    _ = _ := by
      rw [mul_assoc, Nat.mul_comm ((n + 1 + (r + 1)).ascFactorial d),
        Nat.ascFactorial_mul_ascFactorial, Nat.add_right_comm r 1 d]

theorem poly_block_le (d n r : ℕ) (hd : 0 < d) :
    ((n + 1 + (r + d) : ℕ) : ℝ) ^ d / ((n + 1).ascFactorial (r + d + 1) : ℝ) ≤
      (d : ℝ) ^ d / ((n : ℝ) + 1) ^ (r + 1) := by
  have hden : (0 : ℝ) < ((n + 1).ascFactorial (r + d + 1) : ℝ) := by
    exact_mod_cast Nat.ascFactorial_pos n (r + d + 1)
  apply (div_le_div_iff₀ hden (by positivity)).mpr
  exact_mod_cast poly_ascending_bound d n r hd

theorem sigma_le_pow_succ_div_sqrt (k n m : ℕ) (hnm : n + 1 ≤ m) :
    (σ k m : ℝ) ≤ (64 / √((n : ℝ) + 1)) * (m : ℝ) ^ (k + 1) := by
  calc
    _ ≤ 64 * (m : ℝ) ^ k * √(m : ℝ) := sigma_le_pow_sqrt k m (by omega)
    _ = 64 * (m : ℝ) ^ (k + 1) / √(m : ℝ) := by
      simp only [pow_succ, mul_assoc, mul_div_assoc, Real.div_sqrt]
    _ ≤ 64 * (m : ℝ) ^ (k + 1) / √((n : ℝ) + 1) := by
      gcongr
      exact_mod_cast hnm
    _ = _ := by ring

/-- Every omitted actual term obeys a fixed geometric majorant. -/
theorem omittedTerm_le (k n r : ℕ) : blockTerm k (n + 1) (r + (k + 1)) ≤
      (64 / √((n : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ (k + 1) / ((n : ℝ) + 1) ^ (r + 1) := by
  unfold blockTerm
  refine (div_le_div_of_nonneg_right
    (sigma_le_pow_succ_div_sqrt k n _ (by omega)) (Nat.cast_nonneg _)).trans ?_
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (poly_block_le (k + 1) n r (by omega))
      (show 0 ≤ (64 : ℝ) / √((n : ℝ) + 1) by positivity)

theorem hasSum_geometric_recip (C : ℝ) (n : ℕ) (hn : 0 < n) :
    HasSum (fun r : ℕ => C / ((n : ℝ) + 1) ^ (r + 1)) (C / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : (1 : ℝ) / ((n : ℝ) + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  convert! HasSum.mul_left (C / ((n : ℝ) + 1))
    (hasSum_geometric_of_lt_one (by positivity) hq) using 1
  · funext r
    simp only [pow_succ, div_eq_mul_inv, mul_inv_rev]
    ring
  · field_simp [hnR.ne']
    ring

theorem omittedTail_le (k n : ℕ) (hn : 0 < n) : omittedTail k n (k + 1) ≤
      ((64 / √((n : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)) / (n : ℝ) := by
  have hs : Summable (fun r : ℕ => blockTerm k (n + 1) (r + (k + 1))) :=
    (summable_nat_add_iff (k + 1)).2 (summable_blockTerm k (n + 1) (by omega))
  simpa only [omittedTail, (hasSum_geometric_recip _ n hn).tsum_eq] using
    hs.tsum_le_tsum (omittedTerm_le k n) (hasSum_geometric_recip _ n hn).summable

/-- The actual omitted tail is negligible after scaling by the base index. -/
theorem omittedTail_scaled_le (k n : ℕ) (hn : 0 < n) : ((n : ℝ) + 1) * omittedTail k n (k + 1) ≤
      128 * ((k + 1 : ℕ) : ℝ) ^ (k + 1) / √((n : ℝ) + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hratio : ((n : ℝ) + 1) / (n : ℝ) ≤ 2 := (div_le_iff₀ hnR).mpr (by linarith)
  calc
    _ ≤ ((n : ℝ) + 1) * (((64 / √((n : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (omittedTail_le k n hn) (by positivity)
    _ = (((n : ℝ) + 1) / (n : ℝ)) * ((64 / √((n : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)) := by ring
    _ ≤ 2 * ((64 / √((n : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by ring

private theorem sqrt_shift_bound (n h : ℕ) (hh : h ≤ n + 1) :
    √((n + h : ℕ) : ℝ) ≤ 2 * √((n : ℝ) + 1) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
  have hhR : (h : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hh
  push_cast
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

/-- Every finite denominator remainder has a square-root numerator and two
full denominator powers remaining. -/
theorem finiteErr_term_bound (k n j : ℕ) (hn : k + 1 ≤ n) (hj : j < k + 1) :
    0 ≤ (σ k (n + (j + 1)) : ℝ) * stirlingErr j (k + 1) ((n + (j + 1) : ℕ) : ℝ) ∧
      (σ k (n + (j + 1)) : ℝ) * stirlingErr j (k + 1) ((n + (j + 1) : ℕ) : ℝ) ≤
          128 * ((k : ℝ) + 1) ^ (k + 1) * √((n : ℝ) + 1) / ((n : ℝ) + 1) ^ 2 := by
  have hx : (0 : ℝ) < ((n + (j + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n + (j + 1) by omega)
  have hXx : (n : ℝ) + 1 ≤ ((n + (j + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show n + 1 ≤ n + (j + 1) by omega)
  have he := stirlingErr_bounds (k + 1) (k + 1) ((n + (j + 1) : ℕ) : ℝ)
    (by exact_mod_cast (show k + 1 ≤ n + (j + 1) by omega)) j (by omega)
  have hs := sigma_le_pow_sqrt k (n + (j + 1)) (by omega)
  have hroot := sqrt_shift_bound n (j + 1) (by omega)
  refine ⟨mul_nonneg (Nat.cast_nonneg _) he.1, ?_⟩
  calc
    _ ≤ (64 * ((n + (j + 1) : ℕ) : ℝ) ^ k * √((n + (j + 1) : ℕ) : ℝ)) *
        (((k + 1 : ℕ) : ℝ) ^ (k + 1) / ((n + (j + 1) : ℕ) : ℝ) ^ (k + 1 + 1)) :=
      mul_le_mul hs he.2 he.1 (by positivity)
    _ = 64 * ((k : ℝ) + 1) ^ (k + 1) * √((n + (j + 1) : ℕ) : ℝ) / ((n + (j + 1) : ℕ) : ℝ) ^ 2 := by
      rw [show k + 1 + 1 = k + 2 by omega, pow_add]
      push_cast
      field_simp
      ring
    _ ≤ 64 * ((k : ℝ) + 1) ^ (k + 1) * (2 * √((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2 := by gcongr
    _ = _ := by ring

/-- The whole finite error, multiplied by the actual index plus one, is
bounded by a fixed multiple of `sqrt(n+1)/(n+1)`. -/
theorem finiteErr_bounds (k n : ℕ) (hn : k + 1 ≤ n) : 0 ≤ finiteErr k n ∧
      ((n : ℝ) + 1) * finiteErr k n ≤
        128 * ((k : ℝ) + 1) ^ (k + 2) * (√((n : ℝ) + 1) / ((n : ℝ) + 1)) := by
  have hX : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold finiteErr
  have hb := Finset.sum_le_sum (s := Finset.range (k + 1)) (fun j hj =>
    (finiteErr_term_bound k n j hn (Finset.mem_range.mp hj)).2)
  refine ⟨Finset.sum_nonneg (fun j hj =>
    (finiteErr_term_bound k n j hn (Finset.mem_range.mp hj)).1), ?_⟩
  convert! mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (n : ℝ) + 1) using 1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  field_simp

theorem tendsto_finiteErr_mul (k : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * finiteErr k n)
      atTop (𝓝 0) := by
  refine squeeze_zero' (g := fun n : ℕ => 128 * ((k : ℝ) + 1) ^ (k + 2) *
    (√((n : ℝ) + 1) / ((n : ℝ) + 1))) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    exact mul_nonneg (by positivity) (finiteErr_bounds k n hn).1
  · filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    exact (finiteErr_bounds k n hn).2
  · simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_zero] using
      (tendsto_sqrt_div_nat.comp (tendsto_add_atTop_nat 1)).const_mul
        (128 * ((k : ℝ) + 1) ^ (k + 2))

/-- The actual omitted infinite tail vanishes even after multiplication by
the base index plus one. -/
theorem tendsto_omittedTail_mul (k : ℕ) :
    Tendsto (fun n : ℕ =>
      ((n : ℝ) + 1) * omittedTail k n (k + 1))
      atTop (𝓝 0) := by
  refine squeeze_zero' (g := fun n : ℕ =>
    128 * ((k + 1 : ℕ) : ℝ) ^ (k + 1) / √((n : ℝ) + 1)) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall (fun n =>
      mul_nonneg (by positivity) (omittedTail_nonneg k n (k + 1)))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact omittedTail_scaled_le k n (by omega)
  · simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one,
      Real.sqrt_div_self', mul_one_div, mul_zero] using
      (tendsto_sqrt_div_nat.comp (tendsto_add_atTop_nat 1)).const_mul
        (128 * ((k + 1 : ℕ) : ℝ) ^ (k + 1))

/-- The error in the expansion of the actual factorial-series tail is
`o(1/(n+1))`, for every nonnegative divisor-sum exponent. -/
theorem tendsto_tailErr_mul (k : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * tailErr k n)
      atTop (𝓝 0) := by
  simpa only [← mul_add, ← tailErr_eq, add_zero] using
    (tendsto_omittedTail_mul k).add (tendsto_finiteErr_mul k)

theorem tendsto_tailErr (k : ℕ) : Tendsto (tailErr k) atTop (𝓝 0) := by
  simpa only [mul_div_cancel_left₀ _ (Nat.cast_add_one_ne_zero (R := ℝ) _)] using
    (tendsto_tailErr_mul k).div_atTop
    (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ)))

end Erdos252
