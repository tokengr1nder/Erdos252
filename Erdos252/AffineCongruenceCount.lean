import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Exact finite counts for an affine divisibility condition

Over one full period of length `d`, the congruence `d | Q*j+A` has
`gcd(d,Q)` solutions when the gcd divides `A`, and no solutions otherwise.
The proof reduces by the gcd, constructs a residue with a modular inverse,
and applies the exact finite count of one residue class. No limiting or
distribution theorem is used.
-/

namespace Erdos252

/-- A coprime affine congruence has a normalized solution. -/
theorem affineCongruence5_exists_residue_of_coprime {d Q A : ℕ}
    (hd : 0 < d) (hcop : Nat.Coprime Q d) :
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
theorem affineCongruence5_iff_modEq_of_coprime {d Q A v : ℕ}
    (hcop : Nat.Coprime Q d) (hv : d ∣ Q * v + A) (j : ℕ) :
    d ∣ Q * j + A ↔ j ≡ v [MOD d] := by
  constructor
  · intro hj
    have hsum : Q * j + A ≡ Q * v + A [MOD d] :=
      hj.modEq_zero_nat.trans hv.modEq_zero_nat.symm
    exact Nat.ModEq.cancel_left_of_coprime hcop.symm.gcd_eq_one
      (Nat.ModEq.add_right_cancel' A hsum)
  · intro hj
    exact Nat.modEq_zero_iff_dvd.mp (((hj.mul_left Q).add_right A).trans hv.modEq_zero_nat)

/-- Compatibility with the gcd reduces the original congruence to one class modulo `d/gcd`. -/
theorem affineCongruence5_exists_reduced_residue {d Q A : ℕ} (hd : 0 < d)
    (hcompat : Nat.gcd d Q ∣ A) :
    ∃ v < d / Nat.gcd d Q, ∀ j : ℕ,
      d ∣ Q * j + A ↔ j ≡ v [MOD d / Nat.gcd d Q] := by
  let g := Nat.gcd d Q
  have hg : 0 < g := Nat.gcd_pos_of_pos_left Q hd
  have hgd : g ∣ d := Nat.gcd_dvd_left d Q
  have hgQ : g ∣ Q := Nat.gcd_dvd_right d Q
  have hd' : 0 < d / g := Nat.div_pos_iff.mpr ⟨hg, Nat.le_of_dvd hd hgd⟩
  have hcop : Nat.Coprime (Q / g) (d / g) := (Nat.coprime_div_gcd_div_gcd hg).symm
  obtain ⟨v, hvlt, hv⟩ := affineCongruence5_exists_residue_of_coprime (A := A / g) hd' hcop
  refine ⟨v, hvlt, fun j => ?_⟩
  have hred : d ∣ Q * j + A ↔ d / g ∣ (Q / g) * j + A / g := by
    rw [Nat.div_dvd_iff_dvd_mul hgd hg, Nat.mul_add, ← Nat.mul_assoc,
      Nat.mul_div_cancel' hgQ, Nat.mul_div_cancel' hcompat]
  exact hred.trans (affineCongruence5_iff_modEq_of_coprime hcop hv j)

/-- A solution necessarily satisfies the elementary gcd compatibility condition. -/
theorem affineCongruence5_gcd_dvd {d Q A j : ℕ} (hj : d ∣ Q * j + A) :
    Nat.gcd d Q ∣ A := by
  have hsum : Nat.gcd d Q ∣ Q * j + A := (Nat.gcd_dvd_left d Q).trans hj
  have hmul : Nat.gcd d Q ∣ Q * j := dvd_mul_of_dvd_left (Nat.gcd_dvd_right d Q) j
  exact (Nat.dvd_add_iff_right hmul).mpr hsum

/-- Exact full-period count of the affine divisibility condition. -/
theorem affineCongruence5_count_period (Q A d : ℕ) (hd : 0 < d) :
    ((Finset.range d).filter (fun j => d ∣ Q * j + A)).card =
      if Nat.gcd d Q ∣ A then Nat.gcd d Q else 0 := by
  by_cases hcompat : Nat.gcd d Q ∣ A
  · rw [if_pos hcompat]
    obtain ⟨v, hvlt, hv⟩ := affineCongruence5_exists_reduced_residue hd hcompat
    simp_rw [hv]
    rw [← Nat.count_eq_card_filter_range]
    have hg : 0 < Nat.gcd d Q := Nat.gcd_pos_of_pos_left Q hd
    have hd' : 0 < d / Nat.gcd d Q := Nat.div_pos_iff.mpr
      ⟨hg, Nat.le_of_dvd hd (Nat.gcd_dvd_left d Q)⟩
    rw [Nat.count_modEq_card d hd' v,
      Nat.mod_eq_zero_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d Q))]
    simp only [Nat.not_lt_zero, if_false, Nat.add_zero]
    exact Nat.div_div_self (Nat.gcd_dvd_left d Q) hd.ne'
  · rw [if_neg hcompat]
    exact Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr
      (fun j _ hj => hcompat (affineCongruence5_gcd_dvd hj)))

#print axioms affineCongruence5_exists_residue_of_coprime
#print axioms affineCongruence5_iff_modEq_of_coprime
#print axioms affineCongruence5_exists_reduced_residue
#print axioms affineCongruence5_gcd_dvd
#print axioms affineCongruence5_count_period

end Erdos252
