import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Signed binomial weights and vanishing cube moments

The weight at index `i` of an order-`order` forward difference is
`(-1)^(order-i) * choose(order,i)`. Every polynomial moment of degree below
the order vanishes. On a cube of such rows, a coordinate that is absent from
the argument of the test function kills every core of degree below the order.
-/

namespace Erdos252

open scoped BigOperators

/-- The signed binomial row for a forward difference of arbitrary order. -/
def dilationDifferenceWeight (order : ℕ) (i : Fin (order + 1)) : ℤ :=
  (-1) ^ (order - (i : ℕ)) * Nat.choose order (i : ℕ)

/-- All polynomial moments below the difference order vanish. -/
theorem dilationDifferenceWeight_moment {order ell : ℕ} (hell : ell < order) (z d : ℝ) :
    (∑ i : Fin (order + 1),
      (dilationDifferenceWeight order i : ℝ) * (z + d * (i : ℕ)) ^ ell) = 0 := by
  have hh := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
    (P := (Polynomial.C d * Polynomial.X + Polynomial.C z) ^ ell) (n := order)
    ((Polynomial.natDegree_pow_le_of_le ell Polynomial.natDegree_linear_le).trans_lt
      (by omega))) 0
  rw [fwdDiff_iter_eq_sum_shift, Finset.sum_range] at hh
  simpa [dilationDifferenceWeight, add_comm] using hh

/-- The product weight of one cube vertex. -/
def dilationCubeWeight (order : ℕ) {n : ℕ} (e : Fin n → Fin (order + 1)) : ℤ :=
  ∏ j : Fin n, dilationDifferenceWeight order (e j)

theorem dilationCubeWeight_zero_ne_zero (order n : ℕ) :
    dilationCubeWeight order (fun _ : Fin n => (0 : Fin (order + 1))) ≠ 0 := by
  simp [dilationCubeWeight, dilationDifferenceWeight]

theorem dilationCubeWeight_cons (order : ℕ) {n : ℕ} (a : Fin (order + 1))
    (e : Fin n → Fin (order + 1)) :
    dilationCubeWeight order (Fin.cons a e) =
      dilationDifferenceWeight order a * dilationCubeWeight order e := by
  simp [dilationCubeWeight, Fin.prod_univ_succ]

private theorem sum_cube_succ (order : ℕ) {n : ℕ} (G : (Fin (n + 1) → Fin (order + 1)) → ℝ) :
    (∑ e : Fin (n + 1) → Fin (order + 1), G e) =
      ∑ a : Fin (order + 1), ∑ e : Fin n → Fin (order + 1), G (Fin.cons a e) := by
  simpa only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk] using
    ((Fin.consEquiv (fun _ : Fin (n + 1) => Fin (order + 1))).sum_comp G).symm

/-- A coordinate absent from the test argument kills every core of degree
below the difference order. -/
theorem dilationCube_core {order ell : ℕ} (hell : ell < order) {n : ℕ}
    (d c : Fin n → ℝ) (i : Fin n) (hc : c i = 0) (g : ℝ → ℝ) (p q : ℝ) :
    (∑ e : Fin n → Fin (order + 1), (dilationCubeWeight order e : ℝ) *
      ((p + ∑ a, d a * (e a : ℕ)) ^ ell * g (q + ∑ a, c a * (e a : ℕ)))) = 0 := by
  induction n generalizing p q with
  | zero => exact i.elim0
  | succ n ih =>
    rw [sum_cube_succ]
    simp only [dilationCubeWeight_cons, Int.cast_mul, Fin.sum_univ_succ (n := n),
      Fin.cons_zero, Fin.cons_succ, ← add_assoc]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun e _ => ?_
      have hm := congrArg (fun x : ℝ => x * ((dilationCubeWeight order e : ℝ) *
          g (q + ∑ b : Fin n, c b.succ * (e b : ℕ))))
        (dilationDifferenceWeight_moment hell (p + ∑ b : Fin n, d b.succ * (e b : ℕ)) (d 0))
      simp only [hc, zero_mul, add_zero, Finset.sum_mul] at hm ⊢
      exact (Finset.sum_congr rfl fun a _ => by ring).trans hm
    · refine Finset.sum_eq_zero fun a _ => ?_
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [ih (fun b => d b.succ) (fun b => c b.succ) i hc (p + d 0 * a) (q + c 0 * a),
        mul_zero]

#print axioms dilationDifferenceWeight_moment
#print axioms dilationCubeWeight_zero_ne_zero
#print axioms dilationCube_core

end Erdos252
