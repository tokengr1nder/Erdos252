import Erdos252.DilationIrrationality
import Erdos252.DilationZeroCase

/-!
# Erdős problem 252: every natural divisor-sum exponent

The positive degrees use the fixed coprime dilation grid and its isolated
shift. Degree zero uses a direct positive factorial-tail estimate.
Both arguments concern the original infinite divisor-sum series.
-/

namespace Erdos252

theorem irrational_alpha (k : ℕ) : Irrational (alpha k) := by
  cases k with
  | zero => exact irrational_alpha_zero
  | succ k => exact irrational_alpha_pos (Nat.succ_pos k)

/-- The complete factorial divisor-sum irrationality statement. -/
theorem erdos_252 (k : ℕ) :
    Irrational (∑' n : ℕ, (ArithmeticFunction.sigma k n : ℝ) / (n.factorial : ℝ)) :=
  irrational_alpha k

#print axioms irrational_alpha
#print axioms erdos_252

end Erdos252
