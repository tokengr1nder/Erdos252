import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Real.Irrational

namespace Erdos252

open Filter
open scoped Nat BigOperators Topology ArithmeticFunction.sigma

noncomputable section

/-!
# Elementary prerequisites and the factorial tail

Rationality forces late factorial multiples to be integers, the divisor-sum
factorial series converges, an eventually integral null sequence is eventually
zero, and divisor pairing bounds the divisor sum by a square root. On that
basis the reciprocal descending product gets a Stirling expansion of any
order with a nonnegative error, which splits the scaled `alpha k` tail into a
finite main term and an exact error that is `o(1/n)`.
-/

/-- The Erdős 252 factorial series is summable for every exponent `k`. -/
theorem summable_sigma_factorial (k : ℕ) : Summable (fun n : ℕ ↦ (σ k n : ℝ) / (n ! : ℝ)) := by
  refine .of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
    (Real.summable_pow_div_factorial ((2 : ℝ) ^ (k + 1)))
  gcongr
  exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ k n).trans
    (by simpa only [← pow_mul, Nat.mul_comm] using
      Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := n)).le (k + 1) :
      n ^ (k + 1) ≤ (2 ^ (k + 1)) ^ n)

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
def descRecip (h : ℕ) (x : ℝ) : ℝ := 1 / ∏ j ∈ Finset.range h, (x - (j : ℝ))

/-- The Stirling expansion of the `j+1` factor product through reciprocal degree `L`. -/
def stirlingPoly (j L : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range L, (Nat.stirlingSecond i j : ℝ) / x ^ (i + 1)

/-- The exact remainder after the finite Stirling expansion. -/
def stirlingErr (j L : ℕ) (x : ℝ) : ℝ := descRecip (j + 1) x - stirlingPoly j L x

theorem descRecip_succ (h : ℕ) (x : ℝ) : descRecip (h + 1) x = descRecip h x / (x - (h : ℝ)) := by
  simp only [descRecip, Finset.prod_range_succ, div_div]

theorem descRecip_one (x : ℝ) : descRecip 1 x = 1 / x := by
  simp [descRecip]

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
  unfold stirlingErr
  rw [stirlingPoly_recurrence, descRecip_succ (j + 1)]
  push_cast
  field_simp
  ring

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
    have h := descRecip_bounds (j + 1) H x j.succ_pos hH hx
    simpa [stirlingErr, stirlingPoly] using And.intro h.1.le h.2
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
def alpha (k : ℕ) : ℝ := ∑' n : ℕ, (σ k n : ℝ) / (n ! : ℝ)

/-- The actual factorial-series prefix, excluding the term at `n`. -/
def seriesPrefix (k n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, (σ k m : ℝ) / (m.factorial : ℝ)

/-- The actual factorial tail starting at `n`, scaled by `(n-1)!`. -/
def scaledTail (k n : ℕ) : ℝ := ((n - 1).factorial : ℝ) * (alpha k - seriesPrefix k n)

/-- One actual ascending-factorial term in the scaled tail. -/
def blockTerm (k n j : ℕ) : ℝ := (σ k (n + j) : ℝ) / (n.ascFactorial (j + 1) : ℝ)

/-- The generic finite Stirling expansion, in the `n!` indexing convention. -/
def tailMain (k n : ℕ) : ℝ := ∑ j ∈ Finset.range (k + 1),
    (σ k (n + (j + 1)) : ℝ) * stirlingPoly j (k + 1) ((n + (j + 1) : ℕ) : ℝ)

/-- The exact error between the actual generic tail and its finite expansion. -/
def tailErr (k n : ℕ) : ℝ := scaledTail k (n + 1) - tailMain k n

/-- The omitted actual tail after `H` ascending-factorial terms. -/
def omittedTail (k n H : ℕ) : ℝ := ∑' r : ℕ, blockTerm k (n + 1) (r + H)

/-- The finite part of the actual expansion error. -/
def finiteErr (k n : ℕ) : ℝ := ∑ j ∈ Finset.range (k + 1),
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
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hx
  refine ⟨r.den + 1, fun n hn => ?_⟩
  obtain ⟨c, hc⟩ := Nat.dvd_factorial r.pos (by omega : r.den ≤ n - 1)
  obtain ⟨zp, hzp⟩ := seriesPrefix_integral k n
  refine ⟨(c : ℤ) * r.num - zp, ?_⟩
  rw [scaledTail, mul_sub, hzp, hr, Rat.cast_def, hc]
  push_cast
  field_simp

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

theorem blockTerm_nonneg (k n j : ℕ) : 0 ≤ blockTerm k n j :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

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

theorem scaledTail_expansion (k n : ℕ) : scaledTail k (n + 1) = tailMain k n + tailErr k n :=
  (add_sub_cancel _ _).symm

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

theorem tailErr_nonneg (k n : ℕ) (hn : k + 1 ≤ n) : 0 ≤ tailErr k n := by
  rw [tailErr_eq]
  exact add_nonneg (omittedTail_nonneg k n _) (finiteErr_bounds k n hn).1

/-- Both exact error parts are squeezed by multiples of `sqrt(n+1)/(n+1)`. -/
theorem tendsto_tailErr_mul (k : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * tailErr k n) atTop (𝓝 0) := by
  have hb := (eventually_ge_atTop (k + 1)).mono fun n hn => finiteErr_bounds k n hn
  have hf := squeeze_zero' (hb.mono fun n hn => mul_nonneg (by positivity : 0 ≤ (n : ℝ) + 1) hn.1)
    (hb.mono fun _ hn => hn.2)
    (by simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_zero] using
          (tendsto_sqrt_div_nat.comp (tendsto_add_atTop_nat 1)).const_mul
            (128 * ((k : ℝ) + 1) ^ (k + 2)))
  have ho := squeeze_zero'
    (Eventually.of_forall fun n : ℕ =>
      mul_nonneg (by positivity : 0 ≤ (n : ℝ) + 1) (omittedTail_nonneg k n (k + 1)))
    ((eventually_ge_atTop 1).mono fun n hn => omittedTail_scaled_le k n hn)
    (by simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one,
        Real.sqrt_div_self', mul_one_div, mul_zero] using
          (tendsto_sqrt_div_nat.comp (tendsto_add_atTop_nat 1)).const_mul
            (128 * ((k + 1 : ℕ) : ℝ) ^ (k + 1)))
  simpa only [← mul_add, ← tailErr_eq, add_zero] using ho.add hf

theorem tendsto_tailErr (k : ℕ) : Tendsto (tailErr k) atTop (𝓝 0) := by
  simpa only [mul_div_cancel_left₀ _ (Nat.cast_add_one_ne_zero (R := ℝ) _)] using
    (tendsto_tailErr_mul k).div_atTop
    (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ)))

/-!
# Divisor-phase means along arithmetic progressions

Over one period the congruence `d | Q*j+A` has `gcd(d,Q)` solutions when that
gcd divides `A`, so each reciprocal-divisor term has mean `gcd(d,Q)/d^(k+1)`.
Refining by a fresh prime rescales the mean by an exact factor, and two
refinements separating one isolated shift forbid a zero limit of the weighted
phase sum, in every positive degree including degree one.
-/

/-- A coprime affine congruence has a normalized solution. -/
theorem affine_exists_residue {d Q A : ℕ} (hd : 0 < d) (hcop : Nat.Coprime Q d) :
    ∃ v < d, d ∣ Q * v + A := by
  let : NeZero d := ⟨hd.ne'⟩
  let x : ZMod d := -(A : ZMod d) * (Q : ZMod d)⁻¹
  refine ⟨x.val, x.val_lt, ?_⟩
  apply (ZMod.natCast_eq_zero_iff (Q * x.val + A) d).mp
  push_cast
  rw [ZMod.natCast_zmod_val]
  dsimp [x]
  rw [mul_left_comm, ZMod.coe_mul_inv_eq_one Q hcop, mul_one, neg_add_cancel]

/-- Once a coprime affine congruence has a solution, its whole solution set is one residue class. -/
theorem affine_iff_modEq {d Q A v : ℕ} (hcop : Nat.Coprime Q d) (hv : d ∣ Q * v + A) (j : ℕ) :
    d ∣ Q * j + A ↔ j ≡ v [MOD d] := by
  constructor
  · intro hj
    exact Nat.ModEq.cancel_left_of_coprime hcop.symm.gcd_eq_one
      (Nat.ModEq.add_right_cancel' A (hj.modEq_zero_nat.trans hv.modEq_zero_nat.symm))
  · intro hj
    exact Nat.modEq_zero_iff_dvd.mp (((hj.mul_left Q).add_right A).trans hv.modEq_zero_nat)

/-- Compatibility with the gcd reduces the original congruence to one class modulo `d/gcd`. -/
theorem affine_reduced_residue {d Q A : ℕ} (hd : 0 < d) (hcompat : Nat.gcd d Q ∣ A) :
    ∃ v < d / Nat.gcd d Q, ∀ j : ℕ, d ∣ Q * j + A ↔ j ≡ v [MOD d / Nat.gcd d Q] := by
  have hg : 0 < Nat.gcd d Q := Nat.gcd_pos_of_pos_left Q hd
  have hgd : Nat.gcd d Q ∣ d := Nat.gcd_dvd_left d Q
  have hcop : Nat.Coprime (Q / Nat.gcd d Q) (d / Nat.gcd d Q) :=
    (Nat.coprime_div_gcd_div_gcd hg).symm
  obtain ⟨v, hvlt, hv⟩ := affine_exists_residue (A := A / Nat.gcd d Q)
    (Nat.div_pos (Nat.le_of_dvd hd hgd) hg) hcop
  refine ⟨v, hvlt, fun j => ?_⟩
  rw [← affine_iff_modEq hcop hv j, Nat.div_dvd_iff_dvd_mul hgd hg,
    Nat.mul_add, ← Nat.mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right d Q),
    Nat.mul_div_cancel' hcompat]

/-- A solution necessarily satisfies the elementary gcd compatibility condition. -/
theorem affine_gcd_dvd {d Q A j : ℕ} (hj : d ∣ Q * j + A) : Nat.gcd d Q ∣ A :=
  (Nat.dvd_add_iff_right (dvd_mul_of_dvd_left (Nat.gcd_dvd_right d Q) j)).mpr
    ((Nat.gcd_dvd_left d Q).trans hj)

def phase (k n : ℕ) : ℝ := (σ k n : ℝ) / (n : ℝ) ^ k

def divTerm (k d n : ℕ) : ℝ := if d ∣ n then 1 / (d : ℝ) ^ k else 0

/-- The exact progression mean of one reciprocal-divisor term. -/
def meanTerm (k Q A d : ℕ) : ℝ :=
  if Nat.gcd d Q ∣ A then (Nat.gcd d Q : ℝ) / (d : ℝ) ^ (k + 1) else 0

def progMean (k Q A : ℕ) : ℝ := ∑' d : ℕ, meanTerm k Q A d

/-- The phase is the finite sum of its reciprocal divisor powers. -/
theorem hasSum_divTerm (k : ℕ) {n : ℕ} (hn : 0 < n) :
    HasSum (fun d => divTerm k d n) (phase k n) := by
  have hsum : phase k n = ∑ d ∈ n.divisors, divTerm k d n := by
    unfold phase
    rw [ArithmeticFunction.sigma_eq_sum_div]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [divTerm, if_pos (Nat.dvd_of_mem_divisors hd),
      Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd), div_pow, div_right_comm,
      div_self (by positivity : (n : ℝ) ^ k ≠ 0)]
  rw [hsum]
  refine hasSum_sum_of_ne_finset_zero fun d hd => ?_
  simp only [Nat.mem_divisors, hn.ne', ne_eq, not_false_eq_true, and_true] at hd
  simp [divTerm, hd]

/-- Partial sums along the progression just count the affine solutions. -/
theorem divTerm_sum_eq_count (k Q A d N : ℕ) :
    (∑ n ∈ Finset.range N, divTerm k d (Q * n + A)) / (N : ℝ) =
      (((Finset.range N).filter (fun n => d ∣ Q * n + A)).card : ℝ) / (N : ℝ) / (d : ℝ) ^ k := by
  unfold divTerm
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The floor quotient has the expected normalized limit. -/
private theorem tendsto_natDiv_ratio {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 (1 / (d : ℝ))) := by
  simpa only [Function.comp_def, one_div_mul_eq_div, Nat.floor_div_eq_div] using
    (tendsto_nat_floor_mul_div_atTop (a := (1 : ℝ) / (d : ℝ))
      (div_pos zero_lt_one (Nat.cast_pos.mpr hd)).le).comp tendsto_natCast_atTop_atTop

/-- One residue class has exactly its reciprocal density. -/
private theorem tendsto_count_modEq_div {r : ℕ} (hr : 0 < r) (v : ℕ) :
    Tendsto (fun N : ℕ => (Nat.count (· ≡ v [MOD r]) N : ℝ) / (N : ℝ))
      atTop (𝓝 (1 / (r : ℝ))) := by
  have hε : Tendsto (fun N : ℕ => (if v % r < N % r then (1 : ℝ) else 0) / (N : ℝ))
      atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by positivity) (fun N => ?_)
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    gcongr
    split_ifs <;> norm_num
  have key (N : ℕ) : (Nat.count (· ≡ v [MOD r]) N : ℝ) / (N : ℝ) =
      ((N / r : ℕ) : ℝ) / (N : ℝ) + (if v % r < N % r then (1 : ℝ) else 0) / (N : ℝ) := by
    rw [Nat.count_modEq_card N hr v]
    split_ifs <;> push_cast <;> ring
  simpa only [key, add_zero] using (tendsto_natDiv_ratio hr).add hε

/-- Each reciprocal-divisor term has the exact local gcd mean. -/
theorem divTerm_cesaro {k : ℕ} (hk : 0 < k) (Q A d : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, divTerm k d (Q * n + A)) / (N : ℝ)) atTop
      (𝓝 (meanTerm k Q A d)) := by
  simp_rw [divTerm_sum_eq_count, meanTerm]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [zero_pow hk.ne', zero_pow (Nat.succ_ne_zero k)]
  by_cases hcompat : Nat.gcd d Q ∣ A
  · have hg : 0 < Nat.gcd d Q := Nat.gcd_pos_of_pos_left Q hd
    have hgd : Nat.gcd d Q ∣ d := Nat.gcd_dvd_left d Q
    have hr : 0 < d / Nat.gcd d Q := Nat.div_pos (Nat.le_of_dvd hd hgd) hg
    obtain ⟨v, -, hv⟩ := affine_reduced_residue hd hcompat
    simp_rw [hv, ← Nat.count_eq_card_filter_range, if_pos hcompat]
    rw [show (Nat.gcd d Q : ℝ) / (d : ℝ) ^ (k + 1) =
        1 / ((d / Nat.gcd d Q : ℕ) : ℝ) / (d : ℝ) ^ k by
      rw [Nat.cast_div hgd (Nat.cast_ne_zero.mpr hg.ne'), one_div_div, div_div, pow_succ,
        mul_comm ((d : ℝ) ^ k)]]
    exact (tendsto_count_modEq_div hr v).div_const ((d : ℝ) ^ k)
  · have hzero (n : ℕ) : ¬ d ∣ Q * n + A := fun h => hcompat (affine_gcd_dvd h)
    simp [hzero, hcompat]

/-- Positive affine values that are divisible by `d` inject into the multiples
of `d` up to the largest value. -/
theorem affine_count_le_quotient {Q A d : ℕ} (hQ : 0 < Q) (hA : 0 < A) (N : ℕ) :
    ((Finset.range N).filter (fun n => d ∣ Q * n + A)).card ≤ (Q * N + A) / d := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  refine Finset.card_le_card_of_injOn (fun n => Q * n + A) (fun n hn => ?_)
    (fun n _ m _ h => Nat.eq_of_mul_eq_mul_left hQ (Nat.add_right_cancel h))
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hn ⊢
  exact ⟨⟨by omega, Nat.add_le_add_right (Nat.mul_le_mul_left Q hn.1.le) A⟩, hn.2⟩

theorem divTerm_cesaro_bound {k Q A : ℕ} (hk : 0 < k) (hQ : 0 < Q) (hA : 0 < A) (d N : ℕ) :
    ‖(∑ n ∈ Finset.range N, divTerm k d (Q * n + A)) / (N : ℝ)‖ ≤
      ((Q + A : ℕ) : ℝ) / (d : ℝ) ^ (k + 1) := by
  rw [divTerm_sum_eq_count]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.cast_zero, div_zero, zero_div, norm_zero]
    positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [zero_pow hk.ne', zero_pow (Nat.succ_ne_zero k)]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmul : (((Finset.range N).filter (fun n => d ∣ Q * n + A)).card : ℝ) * d ≤
      ((Q + A : ℕ) : ℝ) * N := by
    have hcard := affine_count_le_quotient hQ hA N (d := d)
    exact_mod_cast (Nat.mul_le_mul_right d hcard).trans
      ((Nat.div_mul_le_self _ _).trans (by nlinarith))
  rw [div_div, Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_succ,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hmul (pow_nonneg hdR.le k)]

theorem meanTerm_bounds {k Q : ℕ} (hQ : 0 < Q) (A d : ℕ) :
    0 ≤ meanTerm k Q A d ∧ meanTerm k Q A d ≤ (Q : ℝ) / (d : ℝ) ^ (k + 1) := by
  unfold meanTerm
  split_ifs <;> refine ⟨by positivity, ?_⟩
  · exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.gcd_le_right d hQ)
      (by positivity)
  · positivity

theorem summable_meanTerm {k Q : ℕ} (hk : 0 < k) (hQ : 0 < Q) (A : ℕ) : Summable (meanTerm k Q A) :=
  Summable.of_nonneg_of_le (fun d => (meanTerm_bounds hQ A d).1)
    (fun d => (meanTerm_bounds hQ A d).2)
    (by simpa only [mul_one_div] using
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k + 1)).mul_left (Q : ℝ))

theorem one_le_progMean {k Q : ℕ} (hk : 0 < k) (hQ : 0 < Q) (A : ℕ) : 1 ≤ progMean k Q A := by
  have hh := (summable_meanTerm hk hQ A).le_tsum 1
    (fun d _ => (meanTerm_bounds hQ A d).1)
  simpa [progMean, meanTerm] using hh

/-- The actual phase averages along any positive arithmetic progression. -/
theorem tendsto_progMean {k Q A : ℕ} (hk : 0 < k) (hQ : 0 < Q) (hA : 0 < A) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, phase k (Q * n + A)) / (N : ℝ)) atTop
      (𝓝 (progMean k Q A)) := by
  have hs : Summable (fun d : ℕ => ((Q + A : ℕ) : ℝ) / (d : ℝ) ^ (k + 1)) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k + 1)).mul_left ((Q + A : ℕ) : ℝ)
  refine (tendsto_tsum_of_dominated_convergence hs (fun d => divTerm_cesaro hk Q A d)
    (Eventually.of_forall (fun N d => divTerm_cesaro_bound hk hQ hA d N))).congr'
    (Eventually.of_forall fun N => ?_)
  rw [tsum_div_const, (hasSum_sum fun n _ => hasSum_divTerm k (by omega : 0 < Q * n + A)).tsum_eq]

theorem fresh_prime_residues {ι : Type*} [Fintype ι]
    (r : ι → ℕ) (i₀ : ι) (Q A : ℕ) (hQ : 0 < Q) (hrpos : ∀ i, 0 < r i) :
    ∃ L : ℕ, L.Prime ∧ Q.Coprime L ∧ ∃ v₀ v₁ : ℕ,
      (∀ i, ¬ L ∣ Q * v₀ + A + r i) ∧ (∀ i, L ∣ Q * v₁ + A + r i ↔ r i = r i₀) := by
  classical
  obtain ⟨L, hbound, hp⟩ := Nat.exists_infinite_primes (Q + Finset.univ.sup r + 1)
  have hrL (i : ι) : r i < L := by
    have := Finset.le_sup (f := r) (Finset.mem_univ i)
    omega
  have hcop : Q.Coprime L := (Nat.coprime_of_lt_prime hQ.ne' (by omega) hp).symm
  obtain ⟨v₀, -, hv₀⟩ := affine_exists_residue (A := A) hp.pos hcop
  obtain ⟨v₁, -, hv₁⟩ := affine_exists_residue (A := A + r i₀) hp.pos hcop
  rw [← Nat.add_assoc] at hv₁
  refine ⟨L, hp, hcop, v₀, v₁, fun i hi => ?_, fun i => ⟨fun hi => ?_, fun h => by rwa [h]⟩⟩
  · exact Nat.not_dvd_of_pos_of_lt (hrpos i) (hrL i) ((Nat.dvd_add_iff_right hv₀).mpr hi)
  · exact (Nat.ModEq.add_left_cancel' _
      (hi.modEq_zero_nat.trans hv₁.modEq_zero_nat.symm)).eq_of_lt_of_lt (hrL i) (hrL i₀)

/-- Finite weighted sums commute with limits of their Cesaro averages. -/
theorem tendsto_weightedCesaro {ι : Type*} [Fintype ι] (f : ι → ℕ → ℝ) (c μ : ι → ℝ)
    (hμ : ∀ i, Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f i n) / (N : ℝ)) atTop (𝓝 (μ i))) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, ∑ i, c i * f i n) / (N : ℝ)) atTop
      (𝓝 (∑ i, c i * μ i)) := by
  simpa only [Finset.sum_comm, div_eq_mul_inv, Finset.sum_mul, ← Finset.mul_sum, mul_assoc] using
    tendsto_finsetSum Finset.univ (fun i _ => (hμ i).const_mul (c i))

/-- A positive-step subprogression preserves a sequence limit and its Cesaro limit. -/
theorem tendsto_cesaro_sub {f : ℕ → ℝ} {a : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) {L : ℕ} (hL : 0 < L) (v : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (L * n + v)) / (N : ℝ)) atTop (𝓝 a) := by
  simpa only [div_eq_mul_inv, mul_comm, Function.comp_def, id_eq] using
    (hf.comp ((tendsto_add_atTop_nat v).comp (tendsto_id.const_mul_atTop' hL))).cesaro

/-- An isolated shift contributes exactly its own weighted change in mean. -/
theorem mean_difference {ι : Type*} [Fintype ι] (r : ι → ℕ) (c μ : ι → ℝ) (i₀ : ι) (β κ : ℝ)
    (hunique : ∀ i, r i = r i₀ → i = i₀) :
    (∑ i, c i * (μ i * (β + if r i = r i₀ then κ else 0))) -
        (∑ i, c i * (μ i * β)) = c i₀ * μ i₀ * κ := by
  classical
  have hr (i : ι) : r i = r i₀ ↔ i = i₀ := ⟨hunique i, fun h => h ▸ rfl⟩
  simp_rw [mul_add, Finset.sum_add_distrib, add_sub_cancel_left, mul_ite, mul_zero, hr]
  simp [mul_assoc]

/-- The prime's local gcd is either the prime or one. -/
theorem gcd_eq_prime_or_one {ell : ℕ} (hp : ell.Prime) (d : ℕ) :
    Nat.gcd d ell = if ell ∣ d then ell else 1 := by
  by_cases h : ell ∣ d
  · simp [h, Nat.gcd_eq_right h]
  · simpa [h] using (hp.coprime_iff_not_dvd.mpr h).symm.gcd_eq_one

theorem meanTerm_mul (k : ℕ) {Q ell : ℕ} (hc : ell.Coprime Q) (A d : ℕ) :
    meanTerm k Q A (ell * d) = meanTerm k Q A d / (ell : ℝ) ^ (k + 1) := by
  simp only [meanTerm, hc.gcd_mul_left_cancel]
  split_ifs
  · push_cast
    rw [mul_pow]
    ring
  · simp

theorem progMean_multiples (k : ℕ) {Q ell : ℕ} (hell : 0 < ell) (hc : ell.Coprime Q) (A : ℕ) :
    (∑' d : ℕ, if ell ∣ d then meanTerm k Q A d else 0) = progMean k Q A / (ell : ℝ) ^ (k + 1) := by
  have hs : Function.support (fun d : ℕ =>
      if ell ∣ d then meanTerm k Q A d else 0) ⊆
      Set.range (fun d : ℕ => ell * d) := by
    simp [Set.mem_range, dvd_def, eq_comm]
  simpa [meanTerm_mul k hc, progMean, tsum_div_const] using
    ((mul_right_injective₀ hell.ne').tsum_eq hs).symm

theorem meanTerm_refine (k : ℕ) {Q ell : ℕ} (hp : ell.Prime) (hc : ell.Coprime Q) (B d : ℕ) :
    meanTerm k (Q * ell) B d = meanTerm k Q B d +
        (if ell ∣ B then (ell : ℝ) - 1 else -1) * (if ell ∣ d then meanTerm k Q B d else 0) := by
  simp only [meanTerm]
  rw [hc.symm.gcd_mul, gcd_eq_prime_or_one hp]
  by_cases hd : ell ∣ d
  · simp only [hd, ↓reduceIte]
    have hprod : Nat.gcd d Q * ell ∣ B ↔ Nat.gcd d Q ∣ B ∧ ell ∣ B := by
      exact ⟨fun h => ⟨dvd_of_mul_right_dvd h, dvd_of_mul_left_dvd h⟩,
        fun h => (hc.symm.gcd_left d).mul_dvd_of_dvd_of_dvd h.1 h.2⟩
    by_cases hg : Nat.gcd d Q ∣ B <;> by_cases hB : ell ∣ B <;>
      simp only [hg, hB, hprod, and_self, and_false, false_and, ↓reduceIte]
    all_goals push_cast; ring
  · simp only [hd, ↓reduceIte, Nat.mul_one, mul_zero, add_zero]

theorem progMean_congr (k : ℕ) {Q A B : ℕ} (hAB : Nat.ModEq Q B A) :
    progMean k Q B = progMean k Q A :=
  tsum_congr fun d => by simp only [meanTerm, hAB.dvd_iff (Nat.gcd_dvd_right d Q)]

/-- The exact fresh-prime refinement factor holds in every positive degree. -/
theorem progMean_refine {k Q A B ell : ℕ} (hk : 0 < k) (hQ : 0 < Q)
    (hp : ell.Prime) (hc : ell.Coprime Q) (hAB : Nat.ModEq Q B A) :
    progMean k (Q * ell) B = progMean k Q A *
        (1 - 1 / (ell : ℝ) ^ (k + 1) + if ell ∣ B then 1 / (ell : ℝ) ^ k else 0) := by
  have hs := summable_meanTerm hk hQ B
  have hm : Summable (fun d => if ell ∣ d then meanTerm k Q B d else 0) :=
    hs.summable_of_eq_zero_or_self (fun d => by by_cases h : ell ∣ d <;> simp [h])
  rw [← progMean_congr k hAB]
  change (∑' d, meanTerm k (Q * ell) B d) = _
  simp_rw [meanTerm_refine k hp hc B]
  rw [hs.tsum_add (hm.mul_left _), tsum_mul_left, progMean_multiples k hp.pos hc]
  change progMean k Q B + _ = _
  have he : (ell : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  split_ifs <;> simp only [pow_succ] <;> field_simp <;> ring

/-- Actual phase averages on a fresh-prime subprogression. -/
theorem tendsto_refined_mean {k Q : ℕ} (hk : 0 < k) (hQ : 0 < Q) (A L v : ℕ)
    (hp : L.Prime) (hcop : L.Coprime Q) (hA : 0 < A) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, phase k (Q * (L * n + v) + A)) / (N : ℝ)) atTop
      (𝓝 (progMean k Q A *
        (1 - 1 / (L : ℝ) ^ (k + 1) + if L ∣ Q * v + A then 1 / (L : ℝ) ^ k else 0))) := by
  have hh := tendsto_progMean hk (Nat.mul_pos hQ hp.pos) (by omega : 0 < Q * v + A)
  rw [progMean_refine (A := A) hk hQ hp hcop (by simp [Nat.ModEq])] at hh
  simpa only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] using hh

/-- Every positive degree has the unconditional isolated-shift obstruction.
A fresh prime supplies two refined subprogressions, one missing every shift
and one hitting exactly the distinguished shift. Their weighted phase means
differ by a nonzero amount, so both cannot be the same zero limit. -/
theorem isolated_shift_not_tendsto_zero {k : ℕ} (hk : 0 < k)
    {ι : Type*} [Fintype ι] (r : ι → ℕ) (c : ι → ℝ) (i₀ : ι) (Q A : ℕ)
    (hQ : 0 < Q) (hrpos : ∀ i, 0 < r i)
    (hunique : ∀ i, r i = r i₀ → i = i₀) (hc : c i₀ ≠ 0) :
    ¬ Tendsto (fun n : ℕ => ∑ i, c i * phase k (Q * n + A + r i))
      atTop (𝓝 0) := by
  obtain ⟨L, hp, hcop, v₀, v₁, hmiss, hhit⟩ := fresh_prime_residues r i₀ Q A hQ hrpos
  have hLR : (0 : ℝ) < L := by exact_mod_cast hp.pos
  intro hz
  have hmean (v : ℕ) (i : ι) : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, phase k (Q * (L * n + v) + A + r i)) / (N : ℝ)) atTop
      (𝓝 (progMean k Q (A + r i) *
        (1 - 1 / (L : ℝ) ^ (k + 1) + if L ∣ Q * v + A + r i then 1 / (L : ℝ) ^ k else 0))) := by
    simpa only [Nat.add_assoc] using tendsto_refined_mean hk hQ (A + r i) L v hp
      hcop.symm (by have := hrpos i; omega)
  have heq (v : ℕ) := tendsto_nhds_unique (tendsto_weightedCesaro _ c _ (hmean v))
    (tendsto_cesaro_sub hz hp.pos v)
  have h₀ := heq v₀
  have h₁ := heq v₁
  simp only [hmiss, hhit, ↓reduceIte, add_zero] at h₀ h₁
  have hdiff := mean_difference r c
    (fun i => progMean k Q (A + r i)) i₀
    (1 - 1 / (L : ℝ) ^ (k + 1)) (1 / (L : ℝ) ^ k) hunique
  rw [h₀, h₁, sub_self] at hdiff
  exact (mul_ne_zero (mul_ne_zero hc (lt_of_lt_of_le one_pos
    (one_le_progMean hk hQ (A + r i₀))).ne') (by positivity)) hdiff.symm

/-!
# The dilation grid, the final-order survivor, and the forced zero limit

The dimension `k`, radix `k+2`, factorial spacing and all grid coordinates
remain symbolic; the grid has pairwise coprime multipliers, positive shifts,
an isolated final shift at the zero vertex and compatible squared-modulus
congruences. Signed binomial cube weights cancel every shifted core of degree
at most `k`, leaving a weighted reciprocal-shift sum of the normalized divisor
phase. Eventual integrality of the weighted tail then forces that survivor to
vanish along one CRT progression.
-/

/-- The signed binomial row for a forward difference of arbitrary order. -/
def diffWeight (order : ℕ) (i : Fin (order + 1)) : ℤ :=
  (-1) ^ (order - (i : ℕ)) * Nat.choose order (i : ℕ)

/-- All polynomial moments below the difference order vanish. -/
theorem diffWeight_moment {order ell : ℕ} (hell : ell < order) (z d : ℝ) :
    (∑ i : Fin (order + 1), (diffWeight order i : ℝ) * (z + d * (i : ℕ)) ^ ell) = 0 := by
  have hh := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
    (P := (Polynomial.C d * Polynomial.X + Polynomial.C z) ^ ell) (n := order)
    ((Polynomial.natDegree_pow_le_of_le ell Polynomial.natDegree_linear_le).trans_lt (by omega))) 0
  rw [fwdDiff_iter_eq_sum_shift, Finset.sum_range] at hh
  simpa [diffWeight, add_comm] using hh

/-- The product weight of one cube vertex. -/
def cubeWeight (order : ℕ) {n : ℕ} (e : Fin n → Fin (order + 1)) : ℤ :=
  ∏ j : Fin n, diffWeight order (e j)

theorem cubeWeight_cons (order : ℕ) {n : ℕ} (a : Fin (order + 1)) (e : Fin n → Fin (order + 1)) :
    cubeWeight order (Fin.cons a e) = diffWeight order a * cubeWeight order e := by
  simp [cubeWeight, Fin.prod_univ_succ]

private theorem sum_cube_succ (order : ℕ) {n : ℕ} (G : (Fin (n + 1) → Fin (order + 1)) → ℝ) :
    (∑ e : Fin (n + 1) → Fin (order + 1), G e) =
      ∑ a : Fin (order + 1), ∑ e : Fin n → Fin (order + 1), G (Fin.cons a e) := by
  simpa only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk] using
    ((Fin.consEquiv (fun _ : Fin (n + 1) => Fin (order + 1))).sum_comp G).symm

/-- A coordinate absent from the test argument kills every core of degree
below the difference order. -/
theorem cube_core {order ell : ℕ} (hell : ell < order) {n : ℕ}
    (d c : Fin n → ℝ) (i : Fin n) (hc : c i = 0) (g : ℝ → ℝ) (p q : ℝ) :
    (∑ e : Fin n → Fin (order + 1), (cubeWeight order e : ℝ) *
      ((p + ∑ a, d a * (e a : ℕ)) ^ ell * g (q + ∑ a, c a * (e a : ℕ)))) = 0 := by
  induction n generalizing p q with
  | zero => exact i.elim0
  | succ n ih =>
    rw [sum_cube_succ]
    simp only [cubeWeight_cons, Int.cast_mul, Fin.sum_univ_succ (n := n),
      Fin.cons_zero, Fin.cons_succ, ← add_assoc]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun e _ => ?_
      have hm := congrArg (fun x : ℝ => x * ((cubeWeight order e : ℝ) *
          g (q + ∑ b : Fin n, c b.succ * (e b : ℕ))))
        (diffWeight_moment hell (p + ∑ b : Fin n, d b.succ * (e b : ℕ)) (d 0))
      simp only [hc, zero_mul, add_zero, Finset.sum_mul] at hm ⊢
      exact (Finset.sum_congr rfl fun a _ => by ring).trans hm
    · refine Finset.sum_eq_zero fun a _ => ?_
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [ih (fun b => d b.succ) (fun b => c b.succ) i hc (p + d 0 * a) (q + c 0 * a), mul_zero]

abbrev GridVertex (k : ℕ) := Fin k → Fin (k + 2)

def gridBound (k : ℕ) : ℕ := (k + 2) ^ k - 1

def gridSpacing (k : ℕ) : ℕ := (gridBound k).factorial

def gridBase (k : ℕ) : ℕ := 1 + k * gridSpacing k * gridBound k

def gridIndex (k : ℕ) (e : GridVertex k) : ℕ := ∑ j : Fin k, (e j).val * (k + 2) ^ j.val

def gridWeightedIndex (k : ℕ) (e : GridVertex k) : ℕ :=
  ∑ j : Fin k, (j.val + 1) * (e j).val * (k + 2) ^ j.val

def gridMult (k : ℕ) (e : GridVertex k) : ℕ := gridBase k + gridSpacing k * gridIndex k e

def gridOffset (k : ℕ) (e : GridVertex k) : ℕ := gridSpacing k * gridWeightedIndex k e

def gridShift (k : ℕ) (e : GridVertex k) (j : ℕ) : ℕ := (j + 1) * gridMult k e - gridOffset k e

def gridZero (k : ℕ) : GridVertex k := fun _ => 0

def gridModulus (k : ℕ) : ℕ := ∏ e : GridVertex k, (gridMult k e) ^ 2

theorem gridBound_succ_le {k : ℕ} (hk : 1 ≤ k) : k + 1 ≤ gridBound k := by
  have hh := pow_le_pow_right' (by omega : 1 ≤ k + 2) hk
  simp only [pow_one] at hh
  unfold gridBound
  omega

/-- Every symbolic radix index lies in the prescribed finite interval. -/
theorem gridIndex_le (k : ℕ) (e : GridVertex k) : gridIndex k e ≤ gridBound k :=
  Nat.le_sub_one_of_lt (finFunctionFinEquiv e).isLt

/-- Fixed-length radix encodings distinguish all vertices. -/
theorem gridIndex_injective (k : ℕ) : Function.Injective (gridIndex k) :=
  fun _ _ h => finFunctionFinEquiv.injective (Fin.ext h)

theorem gridIndex_zero (k : ℕ) : gridIndex k (gridZero k) = 0 := by
  simp [gridIndex, gridZero]

/-- The coordinate-weighted index is at most the dimension times the index. -/
theorem gridWeightedIndex_le (k : ℕ) (e : GridVertex k) :
    gridWeightedIndex k e ≤ k * gridIndex k e := by
  unfold gridWeightedIndex gridIndex
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  simpa only [mul_assoc] using Nat.mul_le_mul_right ((e j).val * (k + 2) ^ j.val) j.isLt

theorem gridMult_pos (k : ℕ) (e : GridVertex k) : 0 < gridMult k e :=
  Nat.add_pos_left (Nat.add_pos_left Nat.one_pos _) _

/-- Each multiplier is one modulo the factorial spacing. -/
theorem gridMult_coprime_spacing (k : ℕ) (e : GridVertex k) :
    Nat.Coprime (gridMult k e) (gridSpacing k) := by
  simp only [gridMult, gridBase, Nat.coprime_add_mul_left_left,
    Nat.mul_right_comm k (gridSpacing k) (gridBound k),
    Nat.coprime_add_mul_right_left, Nat.coprime_one_left_eq_true]

private theorem multipliers_coprime_of_index_lt {k : ℕ} {e f : GridVertex k}
    (hef : gridIndex k e < gridIndex k f) :
    Nat.Coprime (gridMult k e) (gridMult k f) := by
  apply Nat.coprime_of_dvd
  intro l hl hle hlf
  have hlD : Nat.Coprime l (gridSpacing k) := (gridMult_coprime_spacing k e).coprime_dvd_left hle
  have hd := Nat.dvd_sub hlf hle
  simp only [gridMult, Nat.add_sub_add_left, ← Nat.mul_sub_left_distrib] at hd
  have hdiff : l ∣ gridIndex k f - gridIndex k e := hlD.dvd_mul_left.mp hd
  have hlF : l ≤ gridBound k := (Nat.le_of_dvd (Nat.sub_pos_of_lt hef) hdiff).trans
      ((Nat.sub_le _ _).trans (gridIndex_le k f))
  exact (hl.coprime_iff_not_dvd.mp hlD) (Nat.dvd_factorial hl.pos hlF)

/-- The complete symbolic-dimensional grid has pairwise coprime multipliers. -/
theorem gridMult_pairwise_coprime (k : ℕ) :
    Pairwise (fun e f : GridVertex k =>
      Nat.Coprime (gridMult k e) (gridMult k f)) := by
  intro e f hef
  rcases lt_or_gt_of_ne (fun h => hef (gridIndex_injective k h)) with h | h
  · exact multipliers_coprime_of_index_lt h
  · exact (multipliers_coprime_of_index_lt h).symm

/-- Every offset is smaller than the base multiplier. -/
theorem gridOffset_lt_base (k : ℕ) (e : GridVertex k) : gridOffset k e < gridBase k := by
  have hDW := Nat.mul_le_mul_left (gridSpacing k) (gridWeightedIndex_le k e)
  have hDI := Nat.mul_le_mul_left (gridSpacing k * k) (gridIndex_le k e)
  unfold gridOffset gridBase
  nlinarith

theorem gridShift_pos (k : ℕ) (e : GridVertex k) (j : ℕ) : 0 < gridShift k e j :=
  Nat.sub_pos_of_lt ((gridOffset_lt_base k e).trans_le
    ((Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_left _ j.succ_pos)))

/-- Natural subtraction in the shift expression is exact. -/
theorem gridShift_add_offset (k : ℕ) (e : GridVertex k) (j : ℕ) :
    gridShift k e j + gridOffset k e = (j + 1) * gridMult k e := by
  have hp := gridShift_pos k e j
  unfold gridShift at hp ⊢
  omega

/-- Among all vertices and all orders at most `k`, the distinguished shift
`(k+1) * base` occurs exactly once: at the zero vertex and the final order. -/
theorem gridShift_eq_succ_base_iff {k : ℕ} (e : GridVertex k) {j : ℕ} (hj : j ≤ k) :
    gridShift k e j = (k + 1) * gridBase k ↔ e = gridZero k ∧ j = k := by
  have hs := gridShift_add_offset k e j
  have hW := Nat.mul_le_mul_left (gridSpacing k) (gridWeightedIndex_le k e)
  have hI := Nat.mul_le_mul_left (gridSpacing k * k) (gridIndex_le k e)
  constructor
  · intro he
    rw [he] at hs
    unfold gridOffset gridMult gridBase at hs
    have hjk : j = k := by
      by_contra hne
      have hlt : j + 1 ≤ k := by omega
      have hmul := Nat.mul_le_mul_right
        (1 + k * gridSpacing k * gridBound k + gridSpacing k * gridIndex k e) hlt
      nlinarith
    rw [hjk] at hs
    refine ⟨gridIndex_injective k ?_, hjk⟩
    rw [gridIndex_zero]
    exact (Nat.mul_eq_zero.mp
      (by nlinarith : gridSpacing k * gridIndex k e = 0)).resolve_left (Nat.factorial_ne_zero _)
  · rintro ⟨rfl, rfl⟩
    simp [gridShift, gridMult, gridOffset, gridIndex, gridWeightedIndex, gridZero]

theorem gridModulus_pos (k : ℕ) : 0 < gridModulus k :=
  Finset.prod_pos (fun e _ => pow_pos (gridMult_pos k e) 2)

/-- All prescribed offset congruences have a simultaneous squared-modulus solution. -/
theorem grid_exists_crt (k : ℕ) :
    ∃ N0 : ℕ, ∀ e : GridVertex k, N0 ≡ gridOffset k e [MOD (gridMult k e) ^ 2] := by
  classical
  let N0 := Nat.chineseRemainderOfFinset (gridOffset k)
    (fun e => (gridMult k e) ^ 2) Finset.univ
    (fun e _ => (pow_pos (gridMult_pos k e) 2).ne')
    (fun e _ f _ hef => ((gridMult_pairwise_coprime k hef).pow_left 2).pow_right 2)
  exact ⟨N0, fun e => N0.property e (Finset.mem_univ e)⟩

def gridWeight (k : ℕ) (e : GridVertex k) : ℤ := cubeWeight (k + 1) e

theorem gridMult_real_eq_cube (k : ℕ) (e : GridVertex k) : (gridMult k e : ℝ) = (gridBase k : ℝ) +
      ∑ i : Fin k, (gridSpacing k : ℝ) * ((k : ℝ) + 2) ^ i.val * (e i).val := by
  unfold gridMult gridIndex
  push_cast
  simp only [Finset.mul_sum, mul_comm, mul_left_comm]

theorem gridShift_real_eq_cube (k : ℕ) (e : GridVertex k) (j : ℕ) :
    (gridShift k e j : ℝ) = ((j : ℝ) + 1) * gridBase k + ∑ i : Fin k, ((j : ℝ) - i.val) *
        ((gridSpacing k : ℝ) * ((k : ℝ) + 2) ^ i.val) * (e i).val := by
  rw [show (gridShift k e j : ℝ) = ((j : ℝ) + 1) * gridMult k e - gridOffset k e from
    eq_sub_of_add_eq (by exact_mod_cast gridShift_add_offset k e j), gridMult_real_eq_cube]
  unfold gridOffset gridWeightedIndex
  push_cast
  simp only [mul_add, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- All lower-order shifted cores cancel on the actual symbolic grid. -/
theorem grid_core_real_cancel {k j ell : ℕ} (hj : j < k) (hell : ell ≤ k) (g : ℝ → ℝ) :
    (∑ e : GridVertex k, (gridWeight k e : ℝ) *
      ((gridMult k e : ℝ) ^ ell * g (gridShift k e j))) = 0 := by
  simp_rw [gridMult_real_eq_cube, gridShift_real_eq_cube]
  exact cube_core (Nat.lt_succ_of_le hell)
    (fun i : Fin k => (gridSpacing k : ℝ) * ((k : ℝ) + 2) ^ i.val)
    (fun i : Fin k => ((j : ℝ) - i.val) * ((gridSpacing k : ℝ) * ((k : ℝ) + 2) ^ i.val))
    ⟨j, hj⟩ (by simp) g _ _

/-- Actual integer weights cancel every real-valued shifted core through degree `k`. -/
theorem grid_core_cancel {k j ell : ℕ} (hj : j < k) (hell : ell ≤ k) (g : ℕ → ℝ) :
    (∑ e : GridVertex k, (gridWeight k e : ℝ) *
      ((gridMult k e : ℝ) ^ ell * g (gridShift k e j))) = 0 := by
  simpa only [Nat.floor_natCast] using grid_core_real_cancel hj hell (fun z => g ⌊z⌋₊)

def gridCore (k N j i : ℕ) : ℝ := ∑ e : GridVertex k, (gridWeight k e : ℝ) *
    ((gridMult k e : ℝ) ^ (i + 1) * ((σ k (N + gridShift k e j) : ℝ) /
        ((N + gridShift k e j : ℕ) : ℝ) ^ (i + 1)))

def finiteMain (k N : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
    (Nat.stirlingSecond i j : ℝ) * gridCore k N j i

def gridCoeff (k : ℕ) (e : GridVertex k) (j : ℕ) : ℝ :=
  (gridWeight k e : ℝ) * (gridMult k e : ℝ) ^ (k + 1) * (Nat.stirlingSecond k j : ℝ)

def survivingMain (k N : ℕ) : ℝ := ∑ e : GridVertex k, ∑ j ∈ Finset.range (k + 1),
    gridCoeff k e j * phase k (N + gridShift k e j) / ((N + gridShift k e j : ℕ) : ℝ)

def survivor (k N : ℕ) : ℝ :=
  ∑ e : GridVertex k, ∑ j ∈ Finset.range (k + 1), gridCoeff k e j * phase k (N + gridShift k e j)

/-- Only the top denominator order survives: lower orders cancel on the grid,
and orders below the shift carry no Stirling coefficient. -/
theorem finiteMain_eq_final (k N : ℕ) : finiteMain k N =
      ∑ j ∈ Finset.range (k + 1), (Nat.stirlingSecond k j : ℝ) * gridCore k N j k := by
  unfold finiteMain
  rw [Finset.sum_eq_single_of_mem k (by simp)]
  · intro i hi hne
    refine Finset.sum_eq_zero fun j hj => ?_
    have hik := Finset.mem_range.mp hi
    have hjk := Finset.mem_range.mp hj
    by_cases hlt : j < k
    · rw [show gridCore k N j i = 0 from grid_core_cancel hlt (by omega)
        (fun s => (σ k (N + s) : ℝ) / ((N + s : ℕ) : ℝ) ^ (i + 1)), mul_zero]
    · rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : i < j), Nat.cast_zero, zero_mul]

/-- Exact expression of the surviving denominator order as raw phases. -/
theorem finiteMain_eq_surviving (k N : ℕ) : finiteMain k N = survivingMain k N := by
  have hdiv (x : ℕ) : (σ k x : ℝ) / (x : ℝ) ^ (k + 1) =
      phase k x / (x : ℝ) := by rw [phase, div_div, pow_succ]
  rw [finiteMain_eq_final]
  unfold gridCore survivingMain gridCoeff
  simp_rw [Finset.mul_sum, hdiv]
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- Reordering the expanded vertex sums gives the same finite main term. -/
theorem finiteMain_vertex (k N : ℕ) : finiteMain k N = ∑ e : GridVertex k, (gridWeight k e : ℝ) *
        (∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1),
          (Nat.stirlingSecond i j : ℝ) * (gridMult k e : ℝ) ^ (i + 1) *
              (σ k (N + gridShift k e j) : ℝ) / ((N + gridShift k e j : ℕ) : ℝ) ^ (i + 1)) := by
  unfold finiteMain gridCore
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- The isolated final-order coefficient never vanishes. -/
theorem gridCoeff_zero_ne_zero (k : ℕ) : gridCoeff k (gridZero k) k ≠ 0 := by
  simp [gridCoeff, Nat.stirlingSecond_self, gridWeight, gridZero, cubeWeight, diffWeight,
    (gridMult_pos k (gridZero k)).ne']

/-- The raw divisor phase is sublinear even in degrees zero and one. -/
theorem tendsto_phase_div_nat (k : ℕ) : Tendsto (fun n : ℕ => phase k n / (n : ℝ)) atTop (𝓝 0) := by
  have hlim := tendsto_sqrt_div_nat.const_mul (64 : ℝ)
  simp only [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun n => by unfold phase; positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa only [phase, mul_div_assoc] using div_le_div_of_nonneg_right
    (sigma_div_le_sqrt k n (by omega)) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

/-- Every fixed coefficient and shift preserves the vanishing ratio limit. -/
theorem grid_main_term_tendsto_zero (k : ℕ) (e : GridVertex k) (h : ℕ) :
    Tendsto (fun N : ℕ =>
      gridCoeff k e h * phase k (N + gridShift k e h) /
        ((N + gridShift k e h : ℕ) : ℝ)) atTop (𝓝 0) := by
  simpa only [mul_zero, mul_div_assoc, Function.comp_apply] using ((tendsto_phase_div_nat k).comp
      (tendsto_add_atTop_nat (gridShift k e h))).const_mul (gridCoeff k e h)

/-- The complete actual surviving main term tends to zero. -/
theorem tendsto_survivingMain (k : ℕ) : Tendsto (survivingMain k) atTop (𝓝 0) := by
  unfold survivingMain
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum (Finset.univ : Finset (GridVertex k))
      (fun e _ => tendsto_finsetSum (Finset.range (k + 1))
        (fun h _ => grid_main_term_tendsto_zero k e h))

/-- Multiplying the main expression by `N` differs from the survivor by a
finite sum of vanishing terms. -/
theorem tendsto_survivor_rescaling (k : ℕ) :
    Tendsto (fun N : ℕ =>
      (N : ℝ) * survivingMain k N - survivor k N)
      atTop (𝓝 0) := by
  have hh := tendsto_finsetSum (Finset.univ : Finset (GridVertex k))
    (fun e _ => tendsto_finsetSum (Finset.range (k + 1))
      (fun h _ => (grid_main_term_tendsto_zero k e h).neg.mul_const
        (gridShift k e h : ℝ)))
  simp only [neg_zero, zero_mul, Finset.sum_const_zero] at hh
  refine hh.congr fun N => ?_
  unfold survivingMain survivor
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun h hh => ?_
  have hx : ((N + gridShift k e h : ℕ) : ℝ) ≠ 0 := by
    have := gridShift_pos k e h
    exact_mod_cast (show N + gridShift k e h ≠ 0 by omega)
  field_simp
  push_cast
  ring

theorem tendsto_affine_atTop (Q A : ℕ) (hQ : 0 < Q) :
    Tendsto (fun t : ℕ => A + Q * t) atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.le_add_left _ _) (tendsto_id.const_mul_atTop' hQ)

def tailIndex (k N : ℕ) (e : GridVertex k) : ℕ := (N - gridOffset k e) / gridMult k e

def GridCongruences (k N : ℕ) : Prop :=
  ∀ e : GridVertex k, N ≡ gridOffset k e [MOD (gridMult k e) ^ 2]

/-- Exact conversion of a shifted quotient into the common shifted argument. -/
theorem tailIndex_factorization (k N : ℕ) (e : GridVertex k) (hN : gridOffset k e ≤ N)
    (hcong : N ≡ gridOffset k e [MOD (gridMult k e) ^ 2]) (j : ℕ) :
    gridMult k e * (tailIndex k N e + (j + 1)) = N + gridShift k e j := by
  have hindex : gridMult k e * tailIndex k N e + gridOffset k e = N := by
    unfold tailIndex
    rw [Nat.mul_comm, Nat.div_mul_cancel ((dvd_pow_self _ (by norm_num : (2 : ℕ) ≠ 0)).trans
      hcong.symm.dvd'), Nat.sub_add_cancel hN]
  have hshift := gridShift_add_offset k e j
  nlinarith

/-- Every retained actual shift is coprime to the grid multiplier. -/
theorem index_coprime {k : ℕ} (hk : 0 < k) (N : ℕ) (e : GridVertex k)
    (hcong : N ≡ gridOffset k e [MOD (gridMult k e) ^ 2]) {j : ℕ} (hj : j ≤ k) :
    Nat.Coprime (gridMult k e) (tailIndex k N e + (j + 1)) := by
  rw [Nat.coprime_add_iff_right (show gridMult k e ∣ tailIndex k N e from
    Nat.dvd_div_of_mul_dvd (by simpa only [pow_two] using hcong.symm.dvd'))]
  exact (gridMult_coprime_spacing k e).coprime_dvd_right
    (Nat.dvd_factorial j.succ_pos ((by omega : j + 1 ≤ k + 1).trans (gridBound_succ_le hk)))

/-- Exact numerator and denominator rescaling for every denominator exponent. -/
theorem tailIndex_term_rescale {k : ℕ} (hk : 0 < k) (N : ℕ) (e : GridVertex k)
    (hN : gridOffset k e ≤ N) (hcong : N ≡ gridOffset k e [MOD (gridMult k e) ^ 2])
    {j : ℕ} (hj : j ≤ k) (i : ℕ) :
    (σ k (gridMult k e) : ℝ) * ((σ k (tailIndex k N e + (j + 1)) : ℝ) /
          ((tailIndex k N e + (j + 1) : ℕ) : ℝ) ^ (i + 1)) =
      (gridMult k e : ℝ) ^ (i + 1) * (σ k (N + gridShift k e j) : ℝ) /
          ((N + gridShift k e j : ℕ) : ℝ) ^ (i + 1) := by
  have hp : (gridMult k e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (gridMult_pos k e).ne'
  rw [← tailIndex_factorization k N e hN hcong j,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (index_coprime hk N e hcong hj)]
  push_cast
  rw [mul_pow, mul_div_mul_left _ _ (pow_ne_zero (i + 1) hp), mul_div_assoc]

/-- The congruences persist along the entire CRT progression. -/
theorem gridCongruences_add_modulus_mul (k N0 t : ℕ) (hN0 : GridCongruences k N0) :
    GridCongruences k (N0 + gridModulus k * t) := by
  intro e
  simpa only [Nat.add_zero] using (hN0 e).add
      ((dvd_mul_of_dvd_left (show (gridMult k e) ^ 2 ∣ gridModulus k from
        Finset.dvd_prod_of_mem (fun f : GridVertex k => (gridMult k f) ^ 2)
          (Finset.mem_univ e)) t).modEq_zero_nat)

def weightedTail (k N : ℕ) : ℝ := ∑ e : GridVertex k, (gridWeight k e : ℝ) *
    (σ k (gridMult k e) : ℝ) * scaledTail k (tailIndex k N e + 1)

def weightedMain (k N : ℕ) : ℝ := ∑ e : GridVertex k, (gridWeight k e : ℝ) *
    (σ k (gridMult k e) : ℝ) * tailMain k (tailIndex k N e)

def weightedError (k N : ℕ) : ℝ := ∑ e : GridVertex k, (gridWeight k e : ℝ) *
    (σ k (gridMult k e) : ℝ) * tailErr k (tailIndex k N e)

theorem weightedTail_split (k N : ℕ) : weightedTail k N = weightedMain k N + weightedError k N := by
  unfold weightedTail weightedMain weightedError
  simp_rw [scaledTail_expansion, mul_add, Finset.sum_add_distrib]

/-- Every actual quotient index tends to infinity on a positive-step progression. -/
theorem tendsto_tailIndex (k Q A : ℕ) (hQ : 0 < Q) (e : GridVertex k) :
    Tendsto (fun t : ℕ => tailIndex k (A + Q * t) e) atTop atTop :=
  (Nat.tendsto_div_const_atTop (gridMult_pos k e).ne').comp
    ((tendsto_sub_atTop_nat (gridOffset k e)).comp (tendsto_affine_atTop Q A hQ))

theorem eventually_weightedTail_integral_prog (k : ℕ) (hx : ¬ Irrational (alpha k)) (A : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∃ z : ℤ, weightedTail k (A + gridModulus k * t) = z := by
  classical
  obtain ⟨K, hK⟩ := eventually_scaledTail_integral k hx
  have hlarge : ∀ᶠ t : ℕ in atTop, ∀ e : GridVertex k, K ≤ tailIndex k (A + gridModulus k * t) e :=
    eventually_all.mpr (fun e =>
      (tendsto_tailIndex k _ A (gridModulus_pos k) e).eventually (eventually_ge_atTop K))
  filter_upwards [hlarge] with t ht
  choose z hz using fun e : GridVertex k => hK _ ((ht e).trans (Nat.le_succ _))
  exact ⟨∑ e : GridVertex k, gridWeight k e * (σ k (gridMult k e) : ℤ) * z e,
    by simp only [weightedTail, hz, Int.cast_sum, Int.cast_mul, Int.cast_natCast]⟩

/-- Cancellation identifies the actual weighted main term with the actual survivor main term. -/
theorem weightedMain_eq_surviving {k : ℕ} (hk : 0 < k) (N : ℕ)
    (hN : gridBase k ≤ N) (hcong : GridCongruences k N) :
    weightedMain k N = survivingMain k N := by
  rw [← finiteMain_eq_surviving, finiteMain_vertex]
  unfold weightedMain
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_assoc, tailMain_eq_range]
  congr 1
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i _ => ?_
  simpa only [mul_assoc, mul_left_comm, mul_div_assoc] using
    congrArg ((Nat.stirlingSecond i j : ℝ) * ·) (tailIndex_term_rescale hk N e
      ((gridOffset_lt_base k e).le.trans hN) (hcong e) (by have := Finset.mem_range.mp hj; omega) i)

/-- The common argument is bounded by one multiplier times its index plus one. -/
theorem tailIndex_common_le (k N : ℕ) (e : GridVertex k) (hN : gridOffset k e ≤ N)
    (hcong : N ≡ gridOffset k e [MOD (gridMult k e) ^ 2]) :
    (N : ℝ) ≤ (gridMult k e : ℝ) * ((tailIndex k N e : ℝ) + 1) := by
  have h := Nat.le_add_right N (gridShift k e 0)
  rw [← tailIndex_factorization k N e hN hcong 0] at h
  exact_mod_cast h

/-- The actual error at one CRT index stays negligible after multiplication
by the common progression argument. -/
theorem tendsto_grid_vertex_error_mul (k A : ℕ) (hA : GridCongruences k A) (e : GridVertex k) :
    Tendsto (fun t : ℕ => ((A + gridModulus k * t : ℕ) : ℝ) *
      tailErr k (tailIndex k (A + gridModulus k * t) e))
      atTop (𝓝 0) := by
  have hindex := tendsto_tailIndex k (gridModulus k) A (gridModulus_pos k) e
  have hlim := ((tendsto_tailErr_mul k).comp hindex).const_mul (gridMult k e : ℝ)
  simp only [Function.comp_apply, mul_zero] at hlim
  have hnonneg := (hindex.eventually (eventually_ge_atTop (k + 1))).mono
    fun t ht => tailErr_nonneg k _ ht
  refine squeeze_zero' (hnonneg.mono fun t ht => mul_nonneg (Nat.cast_nonneg _) ht) ?_ hlim
  filter_upwards [hnonneg, (tendsto_affine_atTop _ A (gridModulus_pos k)).eventually
    (eventually_ge_atTop (gridOffset k e))] with t ht hN
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (tailIndex_common_le k _ e hN (gridCongruences_add_modulus_mul k A t hA e)) ht

/-- Fixed signed weights preserve the vanishing scaled-error limit. -/
theorem tendsto_weightedError_mul (k A : ℕ) (hA : GridCongruences k A) :
    Tendsto (fun t : ℕ => ((A + gridModulus k * t : ℕ) : ℝ) *
      weightedError k (A + gridModulus k * t)) atTop (𝓝 0) := by
  simpa only [weightedError, Finset.mul_sum,
    mul_left_comm, mul_assoc, mul_zero, Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.univ : Finset (GridVertex k)) (fun e _ =>
      (tendsto_grid_vertex_error_mul k A hA e).const_mul
        ((gridWeight k e : ℝ) * (σ k (gridMult k e) : ℝ)))

theorem tendsto_weightedError (k A : ℕ) (hA : GridCongruences k A) :
    Tendsto (fun t : ℕ => weightedError k (A + gridModulus k * t))
      atTop (𝓝 0) := by
  have hN := (tendsto_natCast_atTop_atTop (R := ℝ)).comp
    (tendsto_affine_atTop (gridModulus k) A (gridModulus_pos k))
  refine ((tendsto_weightedError_mul k A hA).div_atTop hN).congr' ?_
  filter_upwards [hN.eventually_ne_atTop 0] with t ht
  exact mul_div_cancel_left₀ _ ht

/-- Eventually, the weighted main term is the surviving main term
along the whole CRT progression. -/
theorem eventually_main_eq_surviving {k : ℕ} (hk : 0 < k) (A : ℕ) (hA : GridCongruences k A) :
    (fun t : ℕ => weightedMain k (A + gridModulus k * t)) =ᶠ[atTop]
      fun t : ℕ => survivingMain k (A + gridModulus k * t) := by
  filter_upwards [(tendsto_affine_atTop _ A (gridModulus_pos k)).eventually
    (eventually_ge_atTop (gridBase k))] with t ht
  exact weightedMain_eq_surviving hk _ ht (gridCongruences_add_modulus_mul k A t hA)

theorem tendsto_weightedTail {k : ℕ} (hk : 0 < k) (A : ℕ) (hA : GridCongruences k A) :
    Tendsto (fun t : ℕ => weightedTail k (A + gridModulus k * t))
      atTop (𝓝 0) := by
  have hmain := ((tendsto_survivingMain k).comp
    (tendsto_affine_atTop _ A (gridModulus_pos k))).congr'
    (eventually_main_eq_surviving hk A hA).symm
  simpa only [← weightedTail_split, add_zero] using hmain.add (tendsto_weightedError k A hA)

/-- Rationality forces the actual generic survivor to vanish on a CRT progression. -/
theorem tendsto_survivor_of_rational {k : ℕ} (hk : 0 < k)
    (hx : ¬ Irrational (alpha k)) (A : ℕ) (hA : GridCongruences k A) :
    Tendsto (fun t : ℕ => survivor k (A + gridModulus k * t))
      atTop (𝓝 0) := by
  have hz := eventually_zero_of_int (tendsto_weightedTail hk A hA)
    (eventually_weightedTail_integral_prog k hx A)
  have hmain : Tendsto (fun t : ℕ => ((A + gridModulus k * t : ℕ) : ℝ) *
      survivingMain k (A + gridModulus k * t)) atTop (𝓝 0) := by
    rw [← neg_zero]
    refine (tendsto_weightedError_mul k A hA).neg.congr' ?_
    filter_upwards [hz, eventually_main_eq_surviving hk A hA] with t ht heq
    rw [← heq, eq_neg_of_add_eq_zero_left ((weightedTail_split k _).symm.trans ht), mul_neg]
  simpa only [Function.comp_apply, sub_sub_cancel, sub_zero] using hmain.sub
    ((tendsto_survivor_rescaling k).comp (tendsto_affine_atTop _ A (gridModulus_pos k)))

/-!
# Irrationality of the divisor-sum factorial series in every positive degree

The final shift at the zero vertex is unique and its coefficient is nonzero,
so rationality would force the actual fixed-grid survivor to tend to zero.
The unconditional arithmetic-progression mean theorem forbids that limit.
-/

abbrev GridTerm (k : ℕ) := GridVertex k × Fin (k + 1)

/-- The exact final-order survivor has no zero limit along any positive-step
arithmetic progression in any positive divisor-power degree. -/
theorem survivor_not_tendsto_zero {k : ℕ} (hk : 0 < k) (Q A : ℕ) (hQ : 0 < Q) :
    ¬ Tendsto (fun n : ℕ => survivor k (Q * n + A)) atTop (𝓝 0) := by
  let i₀ : GridTerm k := ⟨gridZero k, Fin.last k⟩
  have hunique (i : GridTerm k) (hi : gridShift k i.1 i.2 = gridShift k i₀.1 i₀.2) : i = i₀ := by
    obtain ⟨he, hj⟩ := (gridShift_eq_succ_base_iff i.1 (Nat.lt_succ_iff.mp i.2.isLt)).mp
      (hi.trans ((gridShift_eq_succ_base_iff i₀.1 le_rfl).mpr ⟨rfl, rfl⟩))
    exact Prod.ext he (Fin.ext hj)
  simpa only [Fintype.sum_prod_type, survivor, ← Fin.sum_univ_eq_sum_range] using
    isolated_shift_not_tendsto_zero hk
    (fun i : GridTerm k => gridShift k i.1 i.2) (fun i : GridTerm k => gridCoeff k i.1 i.2)
    i₀ Q A hQ (fun i => gridShift_pos k i.1 i.2) hunique (gridCoeff_zero_ne_zero k)

theorem irrational_alpha_pos {k : ℕ} (hk : 0 < k) : Irrational (alpha k) := by
  by_contra hx
  obtain ⟨A, hA⟩ := grid_exists_crt k
  have hz := tendsto_survivor_of_rational hk hx A hA
  apply survivor_not_tendsto_zero hk (gridModulus k) A (gridModulus_pos k)
  simpa only [Nat.add_comm] using hz

/-!
# The zero-degree factorial divisor series

Degree zero is treated using positivity and decay of the actual scaled
factorial tail. No progression-mean assertion at degree zero is used.
-/

/-- Every positive-index actual scaled tail has a positive first term. -/
theorem scaledTail_pos_of_pos (k n : ℕ) (hn : 0 < n) : 0 < scaledTail k n := by
  rw [scaledTail_tsum k n hn]
  refine lt_of_lt_of_le ?_ ((summable_blockTerm k n hn).le_tsum 0
    (fun j _ => blockTerm_nonneg k n j))
  simp only [blockTerm, Nat.ascFactorial_zero, Nat.ascFactorial_succ, Nat.add_zero, Nat.mul_one]
  exact div_pos (Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos k n hn.ne')) (Nat.cast_pos.mpr hn)

/-- The actual zero-degree scaled factorial tail tends to zero. -/
theorem tendsto_scaledTail_zero : Tendsto (scaledTail 0) atTop (𝓝 0) := by
  refine (tendsto_add_atTop_iff_nat 1).mp ?_
  have hmain : Tendsto (fun n => tailMain 0 n) atTop (𝓝 0) := by
    simpa [tailMain_eq_range, phase, Function.comp_def] using
      (tendsto_phase_div_nat 0).comp (tendsto_add_atTop_nat 1)
  simpa only [scaledTail_expansion, add_zero] using hmain.add (tendsto_tailErr 0)

/-- The factorial divisor-count series is irrational. -/
theorem irrational_alpha_zero : Irrational (alpha 0) := by
  by_contra hx
  obtain ⟨N, hN⟩ := eventually_scaledTail_integral 0 hx
  have hz := eventually_zero_of_int tendsto_scaledTail_zero ((eventually_ge_atTop N).mono hN)
  obtain ⟨n, hn, hnpos⟩ := (hz.and (eventually_ge_atTop 1)).exists
  exact (scaledTail_pos_of_pos 0 n (by omega)).ne' hn

/-!
# Erdős problem 252: every natural divisor-sum exponent

The positive degrees use the fixed coprime dilation grid and its isolated
shift. Degree zero uses a direct positive factorial-tail estimate.
Both arguments concern the original infinite divisor-sum series.
-/

theorem irrational_alpha : ∀ k : ℕ, Irrational (alpha k)
  | 0 => irrational_alpha_zero
  | k + 1 => irrational_alpha_pos (Nat.succ_pos k)

/-- The complete factorial divisor-sum irrationality statement. -/
theorem erdos_252 (k : ℕ) :
    Irrational (∑' n : ℕ, (ArithmeticFunction.sigma k n : ℝ) / (n.factorial : ℝ)) :=
  irrational_alpha k

#print axioms erdos_252

end

end Erdos252
