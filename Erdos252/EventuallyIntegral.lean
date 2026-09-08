import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum

/-!
# Vanishing eventually integral sequences

This elementary discreteness lemma is shared by the generic proof and the
historical degree-five proof, without importing either tail construction.
-/

namespace Erdos252

open Filter
open scoped Topology

/-- An eventually integral real sequence tending to zero is eventually zero. -/
theorem dilation5_eventually_zero_of_integral_tendsto {f : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 0))
    (hint : ∀ᶠ n in atTop, ∃ z : ℤ, f n = z) :
    ∀ᶠ n in atTop, f n = 0 := by
  have hsmall : ∀ᶠ n in atTop, |f n| < 1 :=
    ((tendsto_zero_iff_abs_tendsto_zero _).mp hf).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hint, hsmall] with n hn hs
  obtain ⟨z, hz⟩ := hn
  rw [hz] at hs ⊢
  have hzi : |z| < (1 : ℤ) := by exact_mod_cast hs
  have hz0 : z = 0 := by have := abs_lt.mp hzi; omega
  simp only [hz0, Int.cast_zero]

#print axioms dilation5_eventually_zero_of_integral_tendsto

end Erdos252
