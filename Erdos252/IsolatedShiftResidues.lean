import Erdos252.AffineCongruenceCount
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Two arithmetic refinements separating one positive shift

A prime larger than the original modulus and every shift is coprime to the
modulus. One affine residue misses all the positive shifts; another hits
precisely the shifts equal to the distinguished shift. This is pure finite
arithmetic and uses no assertion about sequence means.
-/

namespace Erdos252

theorem isolatedShift5_exists_fresh_prime_residues {ι : Type*} [Fintype ι]
    (r : ι → ℕ) (i₀ : ι) (Q A : ℕ) (hQ : 0 < Q) (hrpos : ∀ i, 0 < r i) :
    ∃ L : ℕ, L.Prime ∧ Q.Coprime L ∧ ∃ v₀ v₁ : ℕ,
      (∀ i, ¬ L ∣ Q * v₀ + A + r i) ∧ (∀ i, L ∣ Q * v₁ + A + r i ↔ r i = r i₀) := by
  classical
  obtain ⟨L, hbound, hp⟩ := Nat.exists_infinite_primes (Q + Finset.univ.sup r + 1)
  have hrL (i : ι) : r i < L := by
    have := Finset.le_sup (f := r) (Finset.mem_univ i)
    omega
  have hcop : Q.Coprime L := (Nat.coprime_of_lt_prime hQ.ne' (by omega) hp).symm
  obtain ⟨v₀, -, hv₀⟩ := affineCongruence5_exists_residue_of_coprime (A := A) hp.pos hcop
  obtain ⟨v₁, -, hv₁⟩ :=
    affineCongruence5_exists_residue_of_coprime (A := A + r i₀) hp.pos hcop
  rw [← Nat.add_assoc] at hv₁
  refine ⟨L, hp, hcop, v₀, v₁, fun i hi => ?_, fun i => ⟨fun hi => ?_, fun h => by rwa [h]⟩⟩
  · exact Nat.not_dvd_of_pos_of_lt (hrpos i) (hrL i) ((Nat.dvd_add_iff_right hv₀).mpr hi)
  · exact (Nat.ModEq.add_left_cancel' _
      (hi.modEq_zero_nat.trans hv₁.modEq_zero_nat.symm)).eq_of_lt_of_lt (hrL i) (hrL i₀)

#print axioms isolatedShift5_exists_fresh_prime_residues

end Erdos252
