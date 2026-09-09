import Erdos252.DilationTailLimit
import Erdos252.DilationGridSurvivorNonzero

/-!
# Irrationality of the divisor-sum factorial series in every positive degree

Rationality would force the actual fixed-grid survivor to tend to zero.
The unconditional arithmetic-progression mean theorem forbids that limit.
-/

namespace Erdos252

open Filter
open scoped Topology

theorem irrational_alpha_pos {k : ℕ} (hk : 0 < k) : Irrational (alpha k) := by
  by_contra hx
  obtain ⟨A, hA⟩ := dilationGridCongruences_exists k
  have hz := tendsto_dilationGridSurvivor_of_rational hk hx A hA
  apply dilationGridSurvivor_not_tendsto_zero hk (dilationGridModulus k) A
    (dilationGridModulus_pos k)
  simpa only [Nat.add_comm] using hz

#print axioms irrational_alpha_pos

end Erdos252
