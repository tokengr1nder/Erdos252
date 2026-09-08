import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A symbolic-dimensional coprime dilation grid

The dimension `k`, radix `k+2`, factorial spacing, and all grid coordinates
remain symbolic. The grid has pairwise coprime multipliers, positive shifts,
an isolated final shift at the zero vertex, and compatible squared-modulus
congruences. This module is entirely arithmetic.
-/

namespace Erdos252

open scoped BigOperators

abbrev DilationGridVertex (k : ℕ) := Fin k → Fin (k + 2)

def dilationGridBound (k : ℕ) : ℕ := (k + 2) ^ k - 1
def dilationGridSpacing (k : ℕ) : ℕ := (dilationGridBound k).factorial
def dilationGridBase (k : ℕ) : ℕ := 1 + k * dilationGridSpacing k * dilationGridBound k
def dilationGridIndex (k : ℕ) (e : DilationGridVertex k) : ℕ :=
  ∑ j : Fin k, (e j).val * (k + 2) ^ j.val
def dilationGridWeightedIndex (k : ℕ) (e : DilationGridVertex k) : ℕ :=
  ∑ j : Fin k, (j.val + 1) * (e j).val * (k + 2) ^ j.val
def dilationGridMultiplier (k : ℕ) (e : DilationGridVertex k) : ℕ :=
  dilationGridBase k + dilationGridSpacing k * dilationGridIndex k e
def dilationGridOffset (k : ℕ) (e : DilationGridVertex k) : ℕ :=
  dilationGridSpacing k * dilationGridWeightedIndex k e
def dilationGridShift (k : ℕ) (e : DilationGridVertex k) (h : ℕ) : ℕ :=
  h * dilationGridMultiplier k e - dilationGridOffset k e
def dilationGridZero (k : ℕ) : DilationGridVertex k := fun _ => 0
def dilationGridModulus (k : ℕ) : ℕ :=
  ∏ e : DilationGridVertex k, (dilationGridMultiplier k e) ^ 2

private theorem sum_digits_eq_ofDigits (b n : ℕ) (e : Fin n → ℕ) :
    (∑ j : Fin n, e j * b ^ j.val) = Nat.ofDigits b (List.ofFn e) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ, List.ofFn_succ, Nat.ofDigits, ← ih]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      simp only [Finset.mul_sum, mul_comm, mul_left_comm, Nat.cast_id]

/-- The index is the usual fixed-length radix encoding. -/
theorem dilationGridIndex_eq_ofDigits (k : ℕ) (e : DilationGridVertex k) :
    dilationGridIndex k e = Nat.ofDigits (k + 2) (List.ofFn (fun j => (e j).val)) :=
  sum_digits_eq_ofDigits (k + 2) k (fun j => (e j).val)

theorem dilationGridBound_succ_le {k : ℕ} (hk : 1 ≤ k) :
    k + 1 ≤ dilationGridBound k := by
  have hh := pow_le_pow_right' (by omega : 1 ≤ k + 2) hk
  simp only [pow_one] at hh
  unfold dilationGridBound
  omega

theorem dilationGridSpacing_pos (k : ℕ) : 0 < dilationGridSpacing k := Nat.factorial_pos _

theorem dilationGridBase_pos (k : ℕ) : 0 < dilationGridBase k := by
  exact Nat.add_pos_left Nat.one_pos _

/-- Every symbolic radix index lies in the prescribed finite interval. -/
theorem dilationGridIndex_le (k : ℕ) (e : DilationGridVertex k) :
    dilationGridIndex k e ≤ dilationGridBound k := by
  have hd : ∀ d ∈ List.ofFn (fun j => (e j).val), d < k + 2 :=
    List.forall_mem_ofFn_iff.mpr (fun j => (e j).isLt)
  have hh := Nat.ofDigits_lt_base_pow_length (by omega : 1 < k + 2) hd
  rw [List.length_ofFn, ← dilationGridIndex_eq_ofDigits] at hh
  unfold dilationGridBound
  omega

/-- Fixed-length radix encodings distinguish all vertices. -/
theorem dilationGridIndex_injective (k : ℕ) : Function.Injective (dilationGridIndex k) := by
  intro e f hef
  rw [dilationGridIndex_eq_ofDigits, dilationGridIndex_eq_ofDigits] at hef
  have hdigits (g : DilationGridVertex k) :
      ∀ d ∈ List.ofFn (fun j => (g j).val), d < k + 2 :=
    List.forall_mem_ofFn_iff.mpr (fun j => (g j).isLt)
  have hlist := Nat.ofDigits_inj_of_len_eq (by omega : 1 < k + 2)
    (L1 := List.ofFn (fun j => (e j).val))
    (L2 := List.ofFn (fun j => (f j).val))
    (by simp) (hdigits e) (hdigits f) hef
  have hfun := List.ofFn_injective hlist
  funext j
  exact Fin.ext (congrFun hfun j)

theorem dilationGridIndex_zero (k : ℕ) : dilationGridIndex k (dilationGridZero k) = 0 := by
  simp [dilationGridIndex, dilationGridZero]

/-- The coordinate-weighted index is at most the dimension times the index. -/
theorem dilationGridWeightedIndex_le (k : ℕ) (e : DilationGridVertex k) :
    dilationGridWeightedIndex k e ≤ k * dilationGridIndex k e := by
  unfold dilationGridWeightedIndex dilationGridIndex
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj : j.val + 1 ≤ k := j.isLt
  simpa only [mul_assoc] using Nat.mul_le_mul_right ((e j).val * (k + 2) ^ j.val) hj

theorem dilationGridMultiplier_pos (k : ℕ) (e : DilationGridVertex k) :
    0 < dilationGridMultiplier k e := by
  exact Nat.add_pos_left (dilationGridBase_pos k) _

theorem dilationGridMultiplier_injective (k : ℕ) :
    Function.Injective (dilationGridMultiplier k) := by
  intro e f hef
  exact dilationGridIndex_injective k
    (Nat.eq_of_mul_eq_mul_left (dilationGridSpacing_pos k) (Nat.add_left_cancel hef))

/-- Each multiplier is one modulo the factorial spacing. -/
theorem dilationGridMultiplier_coprime_spacing (k : ℕ) (e : DilationGridVertex k) :
    Nat.Coprime (dilationGridMultiplier k e) (dilationGridSpacing k) := by
  simp only [dilationGridMultiplier, dilationGridBase, Nat.coprime_add_mul_left_left,
    Nat.mul_right_comm k (dilationGridSpacing k) (dilationGridBound k),
    Nat.coprime_add_mul_right_left, Nat.coprime_one_left_eq_true]

private theorem multipliers_coprime_of_index_lt {k : ℕ} {e f : DilationGridVertex k}
    (hef : dilationGridIndex k e < dilationGridIndex k f) :
    Nat.Coprime (dilationGridMultiplier k e) (dilationGridMultiplier k f) := by
  apply Nat.coprime_of_dvd
  intro l hl hle hlf
  have hlD : Nat.Coprime l (dilationGridSpacing k) :=
    (dilationGridMultiplier_coprime_spacing k e).coprime_dvd_left hle
  have hd := Nat.dvd_sub hlf hle
  simp only [dilationGridMultiplier, Nat.add_sub_add_left,
    ← Nat.mul_sub_left_distrib] at hd
  have hdiff : l ∣ dilationGridIndex k f - dilationGridIndex k e := hlD.dvd_mul_left.mp hd
  have hlF : l ≤ dilationGridBound k :=
    (Nat.le_of_dvd (Nat.sub_pos_of_lt hef) hdiff).trans
      ((Nat.sub_le _ _).trans (dilationGridIndex_le k f))
  have hlFact : l ∣ dilationGridSpacing k := Nat.dvd_factorial hl.pos hlF
  exact (hl.coprime_iff_not_dvd.mp hlD) hlFact

/-- The complete symbolic-dimensional grid has pairwise coprime multipliers. -/
theorem dilationGridMultiplier_pairwise_coprime (k : ℕ) :
    Pairwise (fun e f : DilationGridVertex k =>
      Nat.Coprime (dilationGridMultiplier k e) (dilationGridMultiplier k f)) := by
  intro e f hef
  have hne : dilationGridIndex k e ≠ dilationGridIndex k f :=
    fun h => hef (dilationGridIndex_injective k h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact multipliers_coprime_of_index_lt h
  · exact (multipliers_coprime_of_index_lt h).symm

/-- Every prime factor lies beyond all retained shift orders. -/
theorem dilationGridMultiplier_prime_factor_gt_succ {k : ℕ} (hk : 1 ≤ k)
    (e : DilationGridVertex k) {l : ℕ} (hl : l.Prime)
    (hld : l ∣ dilationGridMultiplier k e) : k + 1 < l := by
  by_contra! hsmall
  have hlD : Nat.Coprime l (dilationGridSpacing k) :=
    (dilationGridMultiplier_coprime_spacing k e).coprime_dvd_left hld
  have hd : l ∣ dilationGridSpacing k :=
    Nat.dvd_factorial hl.pos (hsmall.trans (dilationGridBound_succ_le hk))
  exact (hl.coprime_iff_not_dvd.mp hlD) hd

/-- Every offset is smaller than the base multiplier. -/
theorem dilationGridOffset_lt_base (k : ℕ) (e : DilationGridVertex k) :
    dilationGridOffset k e < dilationGridBase k := by
  have hDW := Nat.mul_le_mul_left (dilationGridSpacing k) (dilationGridWeightedIndex_le k e)
  have hDI := Nat.mul_le_mul_left (dilationGridSpacing k * k) (dilationGridIndex_le k e)
  unfold dilationGridOffset dilationGridBase
  nlinarith

theorem dilationGridShift_pos (k : ℕ) (e : DilationGridVertex k) {h : ℕ} (hh : 1 ≤ h) :
    0 < dilationGridShift k e h := by
  exact Nat.sub_pos_of_lt ((dilationGridOffset_lt_base k e).trans_le
    ((Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_left _ hh)))

/-- Natural subtraction in the shift expression is exact. -/
theorem dilationGridShift_add_offset (k : ℕ) (e : DilationGridVertex k) {h : ℕ}
    (hh : 1 ≤ h) :
    dilationGridShift k e h + dilationGridOffset k e = h * dilationGridMultiplier k e := by
  have hp := dilationGridShift_pos k e hh
  unfold dilationGridShift at hp ⊢
  omega

/-- Every lower-order shift is strictly below the distinguished final shift. -/
theorem dilationGridShift_lt_succ_base (k : ℕ) (e : DilationGridVertex k) {h : ℕ}
    (hh : h ≤ k) : dilationGridShift k e h < (k + 1) * dilationGridBase k := by
  have hI := Nat.mul_le_mul_left (k * dilationGridSpacing k) (dilationGridIndex_le k e)
  have hmul := Nat.mul_le_mul_right (dilationGridMultiplier k e) hh
  have hsub := Nat.sub_le (h * dilationGridMultiplier k e) (dilationGridOffset k e)
  unfold dilationGridShift
  unfold dilationGridMultiplier dilationGridBase at *
  nlinarith

/-- Every final-order shift is at least the distinguished shift. -/
theorem dilationGridShift_succ_lower (k : ℕ) (e : DilationGridVertex k) :
    (k + 1) * dilationGridBase k ≤ dilationGridShift k e (k + 1) := by
  have hs := dilationGridShift_add_offset k e (Nat.succ_pos k)
  have hW := Nat.mul_le_mul_left (dilationGridSpacing k) (dilationGridWeightedIndex_le k e)
  unfold dilationGridOffset dilationGridMultiplier at hs
  nlinarith

/-- Equality at the distinguished final shift occurs only at the zero vertex. -/
theorem dilationGridShift_succ_eq_iff (k : ℕ) (e : DilationGridVertex k) :
    dilationGridShift k e (k + 1) = (k + 1) * dilationGridBase k ↔ e = dilationGridZero k := by
  constructor
  · intro he
    have hs := dilationGridShift_add_offset k e (Nat.succ_pos k)
    have hW := Nat.mul_le_mul_left (dilationGridSpacing k) (dilationGridWeightedIndex_le k e)
    rw [he] at hs
    unfold dilationGridOffset dilationGridMultiplier at hs
    have hmul : dilationGridSpacing k * dilationGridIndex k e = 0 := by nlinarith
    have hI := (Nat.mul_eq_zero.mp hmul).resolve_left (dilationGridSpacing_pos k).ne'
    apply dilationGridIndex_injective k
    rwa [dilationGridIndex_zero]
  · rintro rfl
    simp [dilationGridShift, dilationGridMultiplier, dilationGridOffset,
      dilationGridIndex, dilationGridWeightedIndex, dilationGridZero]

theorem dilationGridModulus_pos (k : ℕ) : 0 < dilationGridModulus k := by
  exact Finset.prod_pos (fun e _ => pow_pos (dilationGridMultiplier_pos k e) 2)

/-- All prescribed offset congruences have a simultaneous squared-modulus solution. -/
theorem dilationGrid_exists_crt (k : ℕ) :
    ∃ N0 : ℕ, ∀ e : DilationGridVertex k,
      N0 ≡ dilationGridOffset k e [MOD (dilationGridMultiplier k e) ^ 2] := by
  classical
  let N0 := Nat.chineseRemainderOfFinset (dilationGridOffset k)
    (fun e => (dilationGridMultiplier k e) ^ 2) Finset.univ
    (fun e _ => (pow_pos (dilationGridMultiplier_pos k e) 2).ne')
    (fun e _ f _ hef =>
      ((dilationGridMultiplier_pairwise_coprime k hef).pow_left 2).pow_right 2)
  exact ⟨N0, fun e => N0.property e (Finset.mem_univ e)⟩

#print axioms dilationGridIndex_eq_ofDigits
#print axioms dilationGridBound_succ_le
#print axioms dilationGridSpacing_pos
#print axioms dilationGridBase_pos
#print axioms dilationGridIndex_le
#print axioms dilationGridIndex_injective
#print axioms dilationGridIndex_zero
#print axioms dilationGridWeightedIndex_le
#print axioms dilationGridMultiplier_pos
#print axioms dilationGridMultiplier_injective
#print axioms dilationGridMultiplier_coprime_spacing
#print axioms dilationGridMultiplier_pairwise_coprime
#print axioms dilationGridMultiplier_prime_factor_gt_succ
#print axioms dilationGridOffset_lt_base
#print axioms dilationGridShift_pos
#print axioms dilationGridShift_add_offset
#print axioms dilationGridShift_lt_succ_base
#print axioms dilationGridShift_succ_lower
#print axioms dilationGridShift_succ_eq_iff
#print axioms dilationGridModulus_pos
#print axioms dilationGrid_exists_crt

end Erdos252
