import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A common sublinear normalized divisor-sum bound for every exponent

Pairing a divisor with its complementary divisor gives a square-root bound
directly. The public constant is kept unchanged; the estimate covers zero,
one, and every larger exponent without the historical divisor-power module.
-/

namespace Erdos252

open scoped BigOperators Topology
open Filter

private theorem divisors_card_le_two_mul_nat_sqrt (n : ℕ) (hn : 0 < n) :
    n.divisors.card ≤ 2 * Nat.sqrt n := by
  let S := Finset.Icc 1 (Nat.sqrt n)
  have hcover : n.divisors ⊆ S ∪ S.image (fun d => n / d) := by
    intro d hd
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hdpos := Nat.pos_of_dvd_of_pos hdvd hn
    have hfactor : n = d * (n / d) := by
      rw [Nat.mul_comm, Nat.div_mul_cancel hdvd]
    rcases Nat.le_sqrt_of_eq_mul hfactor with hsmall | hsmall
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

theorem divisors_card_le_sixty_four_sqrt (n : ℕ) (hn : 0 < n) :
    (n.divisors.card : ℝ) ≤ 64 * Real.sqrt (n : ℝ) := by
  calc
    _ ≤ 2 * (Nat.sqrt n : ℝ) := by
      exact_mod_cast divisors_card_le_two_mul_nat_sqrt n hn
    _ ≤ 2 * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)

theorem sigma_le_divisors_card_mul_pow (k n : ℕ) :
    ArithmeticFunction.sigma k n ≤ n.divisors.card * n ^ k := by
  rw [ArithmeticFunction.sigma_apply]
  calc
    _ ≤ ∑ _d ∈ n.divisors, n ^ k :=
      Finset.sum_le_sum (fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) k)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

theorem sigma_real_le_sixty_four_pow_sqrt (k n : ℕ) (hn : 0 < n) :
    (ArithmeticFunction.sigma k n : ℝ) ≤ 64 * (n : ℝ) ^ k * Real.sqrt (n : ℝ) := by
  have hs : (ArithmeticFunction.sigma k n : ℝ) ≤
      (n.divisors.card : ℝ) * (n : ℝ) ^ k := by
    exact_mod_cast sigma_le_divisors_card_mul_pow k n
  calc
    _ ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ k := hs
    _ ≤ (64 * Real.sqrt (n : ℝ)) * (n : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right (divisors_card_le_sixty_four_sqrt n hn) (by positivity)
    _ = _ := by ring

theorem sigma_normalized_le_sixty_four_sqrt (k n : ℕ) (hn : 0 < n) :
    (ArithmeticFunction.sigma k n : ℝ) / (n : ℝ) ^ k ≤
      64 * Real.sqrt (n : ℝ) := by
  have hpow : (0 : ℝ) < (n : ℝ) ^ k := by positivity
  apply (div_le_iff₀ hpow).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    sigma_real_le_sixty_four_pow_sqrt k n hn

/-- The square-root growth majorant is still sublinear. -/
theorem tendsto_sqrt_nat_div_nat :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  simpa only [Real.sqrt_div_self, Function.comp_def] using
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

#print axioms divisors_card_le_two_mul_nat_sqrt
#print axioms divisors_card_le_sixty_four_sqrt
#print axioms sigma_le_divisors_card_mul_pow
#print axioms sigma_real_le_sixty_four_pow_sqrt
#print axioms sigma_normalized_le_sixty_four_sqrt
#print axioms tendsto_sqrt_nat_div_nat

end Erdos252
