import Erdos252.AffineCongruenceCount
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Two arithmetic refinements separating one positive shift

A prime larger than the original modulus and every shift gives invertibility
of the original modulus. One affine residue misses all the positive shifts;
another hits precisely the shifts equal to the distinguished shift. This is
pure finite arithmetic and uses no assertion about sequence means.
-/

namespace Erdos252

/-- A finite family of shifts and a positive modulus have a larger fresh prime. -/
theorem isolatedShift5_exists_fresh_prime {ι : Type*} [Fintype ι]
    (r : ι → ℕ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ L : ℕ, L.Prime ∧ Q < L ∧ (∀ i, r i < L) ∧ Q.Coprime L := by
  classical
  obtain ⟨L, hbound, hp⟩ := Nat.exists_infinite_primes
    (Q + Finset.univ.sup r + 1)
  have hQL : Q < L := by omega
  have hrL : ∀ i, r i < L := by
    intro i
    have hi : r i ≤ Finset.univ.sup r := Finset.le_sup (Finset.mem_univ i)
    omega
  exact ⟨L, hp, hQL, hrL, (Nat.coprime_of_lt_prime hQ.ne' hQL hp).symm⟩

/-- A zero base residue misses every positive shift smaller than the modulus. -/
theorem isolatedShift5_not_dvd_add {L B r : ℕ}
    (hB : L ∣ B) (hr : 0 < r) (hrL : r < L) : ¬ L ∣ B + r := by
  exact fun hsum => Nat.not_dvd_of_pos_of_lt hr hrL ((Nat.dvd_add_iff_right hB).mpr hsum)

/-- Two shifts smaller than the modulus hit the same base precisely when equal. -/
theorem isolatedShift5_dvd_add_iff {L B r s : ℕ}
    (hB : L ∣ B + s) (hrL : r < L) (hsL : s < L) :
    L ∣ B + r ↔ r = s := by
  constructor
  · intro hr
    have hh : B + r ≡ B + s [MOD L] :=
      hr.modEq_zero_nat.trans hB.modEq_zero_nat.symm
    exact (Nat.ModEq.add_left_cancel' B hh).eq_of_lt_of_lt hrL hsL
  · rintro rfl
    exact hB

/-- An invertible affine map supplies normalized missing and hitting residues. -/
theorem isolatedShift5_exists_two_residues {ι : Type*}
    (r : ι → ℕ) (i₀ : ι) (Q A L : ℕ)
    (hL : 0 < L) (hcop : Q.Coprime L)
    (hrpos : ∀ i, 0 < r i) (hrL : ∀ i, r i < L) :
    ∃ v₀ < L, ∃ v₁ < L,
      L ∣ Q * v₀ + A ∧ L ∣ Q * v₁ + A + r i₀ ∧
      (∀ i, ¬ L ∣ Q * v₀ + A + r i) ∧
      (∀ i, L ∣ Q * v₁ + A + r i ↔ r i = r i₀) := by
  obtain ⟨v₀, hv₀lt, hv₀⟩ :=
    affineCongruence5_exists_residue_of_coprime (A := A) hL hcop
  obtain ⟨v₁, hv₁lt, hv₁⟩ :=
    affineCongruence5_exists_residue_of_coprime (A := A + r i₀) hL hcop
  have hhit : L ∣ Q * v₁ + A + r i₀ := by
    simpa only [Nat.add_assoc] using hv₁
  exact ⟨v₀, hv₀lt, v₁, hv₁lt, hv₀, hhit,
    fun i => isolatedShift5_not_dvd_add hv₀ (hrpos i) (hrL i),
    fun i => isolatedShift5_dvd_add_iff hhit (hrL i) (hrL i₀)⟩

/-- Every finite family of positive shifts has a fresh prime and two normalized
refinements, one missing all shifts and one hitting exactly a prescribed shift. -/
theorem isolatedShift5_exists_fresh_prime_residues {ι : Type*} [Fintype ι]
    (r : ι → ℕ) (i₀ : ι) (Q A : ℕ)
    (hQ : 0 < Q) (hrpos : ∀ i, 0 < r i) :
    ∃ L : ℕ, L.Prime ∧ Q < L ∧ (∀ i, r i < L) ∧ Q.Coprime L ∧
      ∃ v₀ < L, ∃ v₁ < L,
        L ∣ Q * v₀ + A ∧ L ∣ Q * v₁ + A + r i₀ ∧
        (∀ i, ¬ L ∣ Q * v₀ + A + r i) ∧
        (∀ i, L ∣ Q * v₁ + A + r i ↔ r i = r i₀) := by
  obtain ⟨L, hp, hQL, hrL, hcop⟩ := isolatedShift5_exists_fresh_prime r Q hQ
  exact ⟨L, hp, hQL, hrL, hcop,
    isolatedShift5_exists_two_residues r i₀ Q A L hp.pos hcop hrpos hrL⟩

#print axioms isolatedShift5_exists_fresh_prime
#print axioms isolatedShift5_not_dvd_add
#print axioms isolatedShift5_dvd_add_iff
#print axioms isolatedShift5_exists_two_residues
#print axioms isolatedShift5_exists_fresh_prime_residues

end Erdos252
