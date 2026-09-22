import Generalizations.Joint

/-!
# Arbitrary denominator functions forming a divisibility chain

This wrapper presents the joint theorem directly in two functions `a` and
`D`. The step function is recovered as `D(n+1)/D(n)`, not prescribed to be
a polynomial or a factorial ratio. A positive initial scale is harmless.
-/

namespace Erdos252.Generalizations

open Filter
open scoped BigOperators Topology

noncomputable section

def quotientBase (D : ℕ → ℕ) (n : ℕ) : ℕ := D (n + 1) / D n

theorem chain_pos {D : ℕ → ℕ} (h0 : 0 < D 0)
    (hg : ∀ n, 2 * D n ≤ D (n + 1)) (n : ℕ) : 0 < D n := by
  induction n with
  | zero => exact h0
  | succ n ih => exact (Nat.mul_pos (by decide) ih).trans_le (hg n)

theorem quotientBase_ge_two {D : ℕ → ℕ} (h0 : 0 < D 0)
    (hg : ∀ n, 2 * D n ≤ D (n + 1)) (n : ℕ) : 2 ≤ quotientBase D n := by
  exact (Nat.le_div_iff_mul_le (chain_pos h0 hg n)).mpr (hg n)

theorem denom_representation (D q : ℕ → ℕ)
    (hstep : ∀ n, D (n + 1) = D n * q n) (n : ℕ) :
    D n = D 0 * denom q n := by
  induction n with
  | zero => simp
  | succ n ih => rw [hstep, ih, denom_succ, mul_assoc]

/-- A simultaneous theorem for an arbitrary integer numerator and an arbitrary
positive denominator divisibility chain. The denominator need only grow by a
factor of at least two at each step. The residual conditions are substantive
and cannot be omitted, as `telescoping_counterexample` demonstrates. -/
theorem irrational_general_denominator {a b : ℕ → ℤ} {D : ℕ → ℕ}
    (h0 : 0 < D 0) (hdiv : ∀ n, D n ∣ D (n + 1))
    (hg : ∀ n, 2 * D n ≤ D (n + 1))
    (hb : Summable (fun n => (b n : ℝ) / D n))
    (hr : Tendsto (fun n => (residual a b (quotientBase D) n : ℝ) /
      quotientBase D n) atTop (𝓝 0))
    (hne : ¬ ∀ᶠ n in atTop, residual a b (quotientBase D) n = 0) :
    Irrational (∑' n : ℕ, (a n : ℝ) / D (n + 1)) := by
  have hq := quotientBase_ge_two h0 hg
  have hstep (n : ℕ) : D (n + 1) = D n * quotientBase D n :=
    (Nat.mul_div_cancel' (hdiv n)).symm
  have hrep := denom_representation D (quotientBase D) hstep
  have hzero : (D 0 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.ne'
  have hB : Summable (fun n => (b n : ℝ) / denom (quotientBase D) n) := by
    refine (hb.mul_left (D 0 : ℝ)).congr fun n => ?_
    rw [hrep n, Nat.cast_mul]
    field_simp
  have hi := irrational_joint_product_series hq hB hr hne
  have heq : (∑' n : ℕ, (a n : ℝ) / D (n + 1)) =
      (∑' n : ℕ, (a n : ℝ) / denom (quotientBase D) (n + 1)) / (D 0 : ℝ) := by
    rw [← tsum_div_const]
    apply tsum_congr
    intro n
    rw [hrep (n + 1), Nat.cast_mul]
    ring
  rw [heq]
  exact hi.div_natCast h0.ne'

end

end Erdos252.Generalizations
