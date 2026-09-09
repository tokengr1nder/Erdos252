import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum

/-!
# Vanishing eventually integral sequences

An eventually integral real sequence tending to zero is eventually zero.
-/

namespace Erdos252

open Filter
open scoped Topology

theorem dilation5_eventually_zero_of_integral_tendsto {f : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 0))
    (hint : ∀ᶠ n in atTop, ∃ z : ℤ, f n = z) :
    ∀ᶠ n in atTop, f n = 0 := by
  filter_upwards [hint, ((tendsto_zero_iff_abs_tendsto_zero _).mp hf).eventually
    (gt_mem_nhds one_pos)] with n ⟨z, hz⟩ hs
  rw [Function.comp_apply, hz] at hs
  rw [hz]
  exact_mod_cast Int.abs_lt_one_iff.mp (by exact_mod_cast hs)

#print axioms dilation5_eventually_zero_of_integral_tendsto

end Erdos252
