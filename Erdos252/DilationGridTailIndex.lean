import Erdos252.DilationGrid
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Actual tail indices on the symbolic-dimensional dilation grid

Squared multiplier congruences make every quotient index a multiple of its
multiplier. This proves coprimality and exact divisor-sum multiplicativity
through the retained shift order `k+1`. No tail or integrality hypothesis is
introduced in this arithmetic bridge.
-/

namespace Erdos252

open scoped BigOperators

def dilationGridTailIndex (k N : ℕ) (e : DilationGridVertex k) : ℕ :=
  (N - dilationGridOffset k e) / dilationGridMultiplier k e

def DilationGridCongruences (k N : ℕ) : Prop :=
  ∀ e : DilationGridVertex k,
    N ≡ dilationGridOffset k e [MOD (dilationGridMultiplier k e) ^ 2]

def dilationGridTailThreshold (k K : ℕ) : ℕ :=
  dilationGridBase k +
    (dilationGridBase k + dilationGridSpacing k * dilationGridBound k) * K

theorem dilationGridTailIndex_multiplier_dvd (k N : ℕ) (e : DilationGridVertex k)
    (hcong : N ≡ dilationGridOffset k e [MOD (dilationGridMultiplier k e) ^ 2]) :
    dilationGridMultiplier k e ∣ dilationGridTailIndex k N e := by
  unfold dilationGridTailIndex
  apply Nat.dvd_div_of_mul_dvd
  simpa only [pow_two] using hcong.symm.dvd'

theorem dilationGridTailIndex_mul_add_offset (k N : ℕ) (e : DilationGridVertex k)
    (hN : dilationGridOffset k e ≤ N)
    (hcong : N ≡ dilationGridOffset k e [MOD (dilationGridMultiplier k e) ^ 2]) :
    dilationGridMultiplier k e * dilationGridTailIndex k N e + dilationGridOffset k e = N := by
  have hsq : (dilationGridMultiplier k e) ^ 2 ∣ N - dilationGridOffset k e := hcong.symm.dvd'
  have hd : dilationGridMultiplier k e ∣ N - dilationGridOffset k e :=
    (dvd_pow_self _ (by norm_num : (2 : ℕ) ≠ 0)).trans hsq
  unfold dilationGridTailIndex
  rw [Nat.mul_comm, Nat.div_mul_cancel hd, Nat.sub_add_cancel hN]

/-- Exact conversion of a shifted quotient into the common shifted argument. -/
theorem dilationGridTailIndex_factorization (k N : ℕ) (e : DilationGridVertex k)
    (hN : dilationGridOffset k e ≤ N)
    (hcong : N ≡ dilationGridOffset k e [MOD (dilationGridMultiplier k e) ^ 2])
    {h : ℕ} (hh : 1 ≤ h) :
    dilationGridMultiplier k e * (dilationGridTailIndex k N e + h) =
      N + dilationGridShift k e h := by
  have hindex := dilationGridTailIndex_mul_add_offset k N e hN hcong
  have hshift := dilationGridShift_add_offset k e hh
  nlinarith

/-- Every retained actual shift is coprime to the grid multiplier. -/
theorem dilationGridTailIndex_coprime {k : ℕ} (hk : 0 < k) (N : ℕ)
    (e : DilationGridVertex k)
    (hcong : N ≡ dilationGridOffset k e [MOD (dilationGridMultiplier k e) ^ 2])
    {h : ℕ} (hh : h ∈ Finset.Icc 1 (k + 1)) :
    Nat.Coprime (dilationGridMultiplier k e) (dilationGridTailIndex k N e + h) := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hh
  apply Nat.coprime_of_dvd
  intro l hl hlp hln
  have hli : l ∣ dilationGridTailIndex k N e :=
    hlp.trans (dilationGridTailIndex_multiplier_dvd k N e hcong)
  have hlh : l ∣ h := by simpa using Nat.dvd_sub hln hli
  have hlarge := dilationGridMultiplier_prime_factor_gt_succ hk e hl hlp
  have hsmall := Nat.le_of_dvd (show 0 < h by omega) hlh
  omega

/-- Divisor-sum multiplicativity for the actual common shifted numerator. -/
theorem dilationGridTailIndex_sigma_mul {k : ℕ} (hk : 0 < k) (N : ℕ)
    (e : DilationGridVertex k) (hN : dilationGridOffset k e ≤ N)
    (hcong : N ≡ dilationGridOffset k e [MOD (dilationGridMultiplier k e) ^ 2])
    {h : ℕ} (hh : h ∈ Finset.Icc 1 (k + 1)) :
    ArithmeticFunction.sigma k (dilationGridMultiplier k e) *
        ArithmeticFunction.sigma k (dilationGridTailIndex k N e + h) =
      ArithmeticFunction.sigma k (N + dilationGridShift k e h) := by
  rw [← dilationGridTailIndex_factorization k N e hN hcong (Finset.mem_Icc.mp hh).1]
  exact (ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    (dilationGridTailIndex_coprime hk N e hcong hh)).symm

/-- Exact numerator and denominator rescaling for every denominator exponent. -/
theorem dilationGridTailIndex_term_rescale {k : ℕ} (hk : 0 < k) (N : ℕ)
    (e : DilationGridVertex k) (hN : dilationGridOffset k e ≤ N)
    (hcong : N ≡ dilationGridOffset k e [MOD (dilationGridMultiplier k e) ^ 2])
    {h : ℕ} (hh : h ∈ Finset.Icc 1 (k + 1)) (ell : ℕ) :
    (ArithmeticFunction.sigma k (dilationGridMultiplier k e) : ℝ) *
        ((ArithmeticFunction.sigma k (dilationGridTailIndex k N e + h) : ℝ) /
          ((dilationGridTailIndex k N e + h : ℕ) : ℝ) ^ ell) =
      (dilationGridMultiplier k e : ℝ) ^ ell *
        (ArithmeticFunction.sigma k (N + dilationGridShift k e h) : ℝ) /
          ((N + dilationGridShift k e h : ℕ) : ℝ) ^ ell := by
  have hp : (dilationGridMultiplier k e : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (dilationGridMultiplier_pos k e).ne'
  have hs : (ArithmeticFunction.sigma k (N + dilationGridShift k e h) : ℝ) =
      (ArithmeticFunction.sigma k (dilationGridMultiplier k e) : ℝ) *
        (ArithmeticFunction.sigma k (dilationGridTailIndex k N e + h) : ℝ) := by
    exact_mod_cast (dilationGridTailIndex_sigma_mul hk N e hN hcong hh).symm
  rw [hs, ← dilationGridTailIndex_factorization k N e hN hcong (Finset.mem_Icc.mp hh).1,
    Nat.cast_mul, mul_pow]
  rw [mul_div_mul_left _ _ (pow_ne_zero ell hp), mul_div_assoc]

theorem dilationGridTailThreshold_vertex_le (k K : ℕ) (e : DilationGridVertex k) :
    dilationGridOffset k e + dilationGridMultiplier k e * K ≤ dilationGridTailThreshold k K := by
  have ho := (dilationGridOffset_lt_base k e).le
  have hp : dilationGridMultiplier k e ≤
      dilationGridBase k + dilationGridSpacing k * dilationGridBound k := by
    unfold dilationGridMultiplier
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_left (dilationGridSpacing k) (dilationGridIndex_le k e)) _
  exact Nat.add_le_add ho (Nat.mul_le_mul_right K hp)

/-- One explicit threshold makes all quotient indices simultaneously large. -/
theorem dilationGridTailIndex_ge (k N K : ℕ)
    (hN : dilationGridTailThreshold k K ≤ N) (e : DilationGridVertex k) :
    K ≤ dilationGridTailIndex k N e := by
  have hv := (dilationGridTailThreshold_vertex_le k K e).trans hN
  unfold dilationGridTailIndex
  apply (Nat.le_div_iff_mul_le (dilationGridMultiplier_pos k e)).mpr
  have hmul : dilationGridMultiplier k e * K ≤ N - dilationGridOffset k e := by omega
  simpa only [Nat.mul_comm] using hmul

theorem dilationGridTailThreshold_offset_le (k N K : ℕ)
    (hN : dilationGridTailThreshold k K ≤ N) (e : DilationGridVertex k) :
    dilationGridOffset k e ≤ N := by
  have hv := (dilationGridTailThreshold_vertex_le k K e).trans hN
  omega

theorem dilationGridMultiplier_sq_dvd_modulus (k : ℕ) (e : DilationGridVertex k) :
    (dilationGridMultiplier k e) ^ 2 ∣ dilationGridModulus k := by
  classical
  unfold dilationGridModulus
  exact Finset.dvd_prod_of_mem
    (fun f : DilationGridVertex k => (dilationGridMultiplier k f) ^ 2) (Finset.mem_univ e)

/-- The congruences persist along the entire CRT progression. -/
theorem dilationGridCongruences_add_modulus_mul (k N0 t : ℕ)
    (hN0 : DilationGridCongruences k N0) :
    DilationGridCongruences k (N0 + dilationGridModulus k * t) := by
  intro e
  have hd := dilationGridMultiplier_sq_dvd_modulus k e
  change (N0 + dilationGridModulus k * t) % (dilationGridMultiplier k e) ^ 2 =
    dilationGridOffset k e % (dilationGridMultiplier k e) ^ 2
  simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hd, zero_mul,
    Nat.zero_mod, Nat.add_zero, Nat.mod_mod] using hN0 e

theorem dilationGridCongruences_exists (k : ℕ) :
    ∃ N0 : ℕ, DilationGridCongruences k N0 := dilationGrid_exists_crt k

#print axioms dilationGridTailIndex_multiplier_dvd
#print axioms dilationGridTailIndex_mul_add_offset
#print axioms dilationGridTailIndex_factorization
#print axioms dilationGridTailIndex_coprime
#print axioms dilationGridTailIndex_sigma_mul
#print axioms dilationGridTailIndex_term_rescale
#print axioms dilationGridTailThreshold_vertex_le
#print axioms dilationGridTailIndex_ge
#print axioms dilationGridTailThreshold_offset_le
#print axioms dilationGridMultiplier_sq_dvd_modulus
#print axioms dilationGridCongruences_add_modulus_mul
#print axioms dilationGridCongruences_exists

end Erdos252
