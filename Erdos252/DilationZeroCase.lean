import Erdos252.FactorialTail
import Erdos252.DilationSurvivingMain

/-!
# The zero-degree factorial divisor series

Degree zero is treated using positivity and decay of the actual scaled
factorial tail. No progression-mean assertion at degree zero is used.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology ArithmeticFunction.sigma

/-- Every positive-index actual scaled tail has a positive first term. -/
theorem scaledTail_pos_of_pos (k n : ℕ) (hn : 0 < n) : 0 < scaledTail k n := by
  rw [scaledTail_tsum k n hn]
  refine lt_of_lt_of_le ?_ ((summable_blockTerm k n hn).le_tsum 0
    (fun j _ => blockTerm_nonneg k n j))
  simp only [blockTerm, Nat.ascFactorial_zero, Nat.ascFactorial_succ, Nat.add_zero, Nat.mul_one]
  exact div_pos (Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos k n hn.ne')) (Nat.cast_pos.mpr hn)

/-- The elementary divisor-count square-root bound forces the zero-degree main
term to tend to zero. -/
theorem tendsto_tailMain_zero : Tendsto (tailMain 0) atTop (𝓝 0) := by
  change Tendsto (fun n => tailMain 0 n) atTop (𝓝 0)
  simpa [tailMain_eq_range, phase, Function.comp_def] using
    (tendsto_phase_div_nat 0).comp (tendsto_add_atTop_nat 1)

/-- The actual zero-degree scaled factorial tail tends to zero. -/
theorem tendsto_scaledTail_zero : Tendsto (scaledTail 0) atTop (𝓝 0) := by
  refine (tendsto_add_atTop_iff_nat 1).mp ?_
  simpa only [scaledTail_expansion, add_zero] using tendsto_tailMain_zero.add (tendsto_tailErr 0)

/-- The factorial divisor-count series is irrational. -/
theorem irrational_alpha_zero : Irrational (alpha 0) := by
  by_contra hx
  obtain ⟨N, hN⟩ := eventually_scaledTail_integral 0 hx
  have hz := eventually_zero_of_int tendsto_scaledTail_zero ((eventually_ge_atTop N).mono hN)
  obtain ⟨n, hn, hnpos⟩ := (hz.and (eventually_ge_atTop 1)).exists
  exact (scaledTail_pos_of_pos 0 n (by omega)).ne' hn

end Erdos252
