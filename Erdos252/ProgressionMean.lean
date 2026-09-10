import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Divisor-phase means along arithmetic progressions

Over one period the congruence `d | Q*j+A` has `gcd(d,Q)` solutions when that
gcd divides `A`, so each reciprocal-divisor term has mean `gcd(d,Q)/d^(k+1)`.
Refining by a fresh prime rescales the mean by an exact factor, and two
refinements separating one isolated shift forbid a zero limit of the weighted
phase sum, in every positive degree including degree one.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology ArithmeticFunction.sigma

noncomputable section

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
  · have hzero (N : ℕ) : ((Finset.range N).filter (fun n => d ∣ Q * n + A)).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr
        fun n _ hn => hcompat (affine_gcd_dvd hn))
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
  have hlin : Tendsto (fun n : ℕ => L * n + v) atTop atTop :=
    (tendsto_add_atTop_nat v).comp (tendsto_id.const_mul_atTop' hL)
  simpa only [div_eq_mul_inv, mul_comm, Function.comp_def] using (hf.comp hlin).cesaro

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

theorem meanTerm_congr (k : ℕ) {Q A B : ℕ} (hAB : Nat.ModEq Q B A) (d : ℕ) :
    meanTerm k Q B d = meanTerm k Q A d := by
  simp only [meanTerm, hAB.dvd_iff (Nat.gcd_dvd_right d Q)]

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
    progMean k Q B = progMean k Q A := by
  unfold progMean
  exact tsum_congr (meanTerm_congr k hAB)

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
  have hAB : Nat.ModEq Q (Q * v + A) A := by
    unfold Nat.ModEq
    simp
  have hh := tendsto_progMean hk (Nat.mul_pos hQ hp.pos) (by omega : 0 < Q * v + A)
  rw [progMean_refine hk hQ hp hcop hAB] at hh
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

end

end Erdos252
