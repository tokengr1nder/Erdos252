import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring

/-!
# Symbolic binomial differences for the dilation method

The order is arbitrary. The forward orientation of the signed binomial row
is used, so the weight at index `i` is `(-1)^(order-i) * choose(order,i)`.
This differs from the reverse orientation by one overall sign and agrees
with it for even orders. All powers strictly below the order vanish.
-/

namespace Erdos252

open scoped BigOperators

/-- The signed binomial row for a forward difference of arbitrary order. -/
def dilationDifferenceWeight (order : ℕ) (i : Fin (order + 1)) : ℚ :=
  (-1 : ℚ) ^ (order - (i : ℕ)) * (Nat.choose order (i : ℕ) : ℚ)

/-- All polynomial moments below the symbolic difference order vanish. -/
theorem dilationDifferenceWeight_moment {order ell : ℕ} (hell : ell < order)
    (z d : ℚ) :
    (∑ i : Fin (order + 1),
      dilationDifferenceWeight order i * (z + d * (i : ℕ)) ^ ell) = 0 := by
  let P : Polynomial ℚ := (Polynomial.C z + Polynomial.C d * Polynomial.X) ^ ell
  have hlinear : (Polynomial.C z + Polynomial.C d * Polynomial.X).natDegree ≤ 1 := by
    simpa only [Polynomial.natDegree_C_add, Polynomial.natDegree_X] using
      Polynomial.natDegree_C_mul_le d Polynomial.X
  have hdeg : P.natDegree < order := by
    exact lt_of_le_of_lt (by simpa only [Nat.mul_one] using
      Polynomial.natDegree_pow_le_of_le ell hlinear) hell
  have hh := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg) (0 : ℚ)
  rw [fwdDiff_iter_eq_sum_shift] at hh
  simpa [P, dilationDifferenceWeight, zsmul_eq_mul, nsmul_eq_mul,
    Finset.sum_range] using hh

/-- A tilted finite difference preserves the matching linear expression. -/
def dilationDifference (order : ℕ) (j d : ℚ)
    (F : ℚ → ℚ → ℚ) (p t : ℚ) : ℚ :=
  ∑ i : Fin (order + 1), dilationDifferenceWeight order i *
    F (p + d * (i : ℕ)) (t + j * d * (i : ℕ))

/-- A matching tilt kills every core power below the difference order. -/
theorem dilationDifference_core {order ell : ℕ} (hell : ell < order)
    (j d : ℚ) (g : ℚ → ℚ) (p t : ℚ) :
    dilationDifference order j d
      (fun a b => a ^ ell * g (j * a - b)) p t = 0 := by
  unfold dilationDifference
  simp_rw [mul_add, mul_assoc, add_sub_add_right_eq_sub, ← mul_assoc]
  rw [← Finset.sum_mul, dilationDifferenceWeight_moment hell, zero_mul]

/-- Tilted differences commute, including when their orders are different. -/
theorem dilationDifference_comm (order₁ order₂ : ℕ) (j d h e : ℚ)
    (F : ℚ → ℚ → ℚ) (p t : ℚ) :
    dilationDifference order₁ j d (dilationDifference order₂ h e F) p t =
      dilationDifference order₂ h e (dilationDifference order₁ j d F) p t := by
  unfold dilationDifference
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [add_right_comm, mul_left_comm]

theorem dilationDifference_zero (order : ℕ) (j d p t : ℚ) :
    dilationDifference order j d (fun _ _ => 0) p t = 0 := by
  simp [dilationDifference]

/-- The zero vertex has a nonzero coefficient in every order. -/
theorem dilationDifferenceWeight_zero_ne_zero (order : ℕ) :
    dilationDifferenceWeight order 0 ≠ 0 := by
  simp [dilationDifferenceWeight]

#print axioms dilationDifferenceWeight_moment
#print axioms dilationDifference_core
#print axioms dilationDifference_comm
#print axioms dilationDifference_zero
#print axioms dilationDifferenceWeight_zero_ne_zero

end Erdos252
