import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp

/-!
# Rational numbers and factorial denominators

This file records the elementary integrality step in the factorial-series
method for Erdős Problem 252.
-/

namespace Erdos252

/-- If a real number is rational, then all sufficiently late factorial
multiples of it are integers. -/
theorem eventually_factorial_mul_eq_int_of_not_irrational {x : ℝ}
    (hx : ¬ Irrational x) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ z : ℤ, (n.factorial : ℝ) * x = z := by
  obtain ⟨r, rfl⟩ := exists_rat_of_not_irrational hx
  refine ⟨r.den, fun n hn ↦ ?_⟩
  obtain ⟨c, hc⟩ := Nat.dvd_factorial r.pos hn
  refine ⟨(c : ℤ) * r.num, ?_⟩
  rw [Rat.cast_def, hc]
  push_cast
  field_simp

#print axioms eventually_factorial_mul_eq_int_of_not_irrational

end Erdos252
