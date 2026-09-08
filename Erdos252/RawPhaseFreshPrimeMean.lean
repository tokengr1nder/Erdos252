import Erdos252.RawPhaseProgressionMean

/-!
# Fresh-prime refinement of divisor-phase means in arbitrary degree

For `k ≥ 2`, refinement by a prime not dividing the old modulus changes the
mean by the exact factor `1 - ell^(-(k+1)) + 1_hit * ell^(-k)`.
-/

namespace Erdos252

open scoped BigOperators

noncomputable section

theorem rawPhaseProgressionMeanTerm_mul (k : ℕ) {Q ell : ℕ}
    (hc : ell.Coprime Q) (A d : ℕ) :
    rawPhaseProgressionMeanTerm k Q A (ell * d) =
      rawPhaseProgressionMeanTerm k Q A d / (ell : ℝ) ^ (k + 1) := by
  rw [rawPhaseProgressionMeanTerm_eq_gcd,
    rawPhaseProgressionMeanTerm_eq_gcd, hc.gcd_mul_left_cancel]
  split_ifs
  · push_cast
    rw [mul_pow]
    ring
  · simp

theorem rawPhaseProgressionMean_multiples (k : ℕ) {Q ell : ℕ}
    (hell : 0 < ell) (hc : ell.Coprime Q) (A : ℕ) :
    (∑' d : ℕ, if ell ∣ d then rawPhaseProgressionMeanTerm k Q A d else 0) =
      rawPhaseProgressionMean k Q A / (ell : ℝ) ^ (k + 1) := by
  have hinj : Function.Injective (fun d : ℕ => ell * d) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left hell h
  have hs : Function.support (fun d : ℕ =>
      if ell ∣ d then rawPhaseProgressionMeanTerm k Q A d else 0) ⊆
      Set.range (fun d : ℕ => ell * d) := by
    intro d hd
    by_cases hh : ell ∣ d
    · obtain ⟨j, hj⟩ := hh
      exact ⟨j, hj.symm⟩
    · exact False.elim (hd (by simp [hh]))
  rw [← hinj.tsum_eq hs]
  simp only [dvd_mul_right, ↓reduceIte]
  simp_rw [rawPhaseProgressionMeanTerm_mul k hc]
  rw [tsum_div_const]
  rfl

theorem rawPhaseProgressionMeanTerm_congr (k : ℕ) {Q A B : ℕ}
    (hAB : Nat.ModEq Q B A) (d : ℕ) :
    rawPhaseProgressionMeanTerm k Q B d = rawPhaseProgressionMeanTerm k Q A d := by
  simp only [rawPhaseProgressionMeanTerm_eq_gcd,
    hAB.dvd_iff (Nat.gcd_dvd_right d Q)]

theorem rawPhaseProgressionMeanTerm_refine (k : ℕ) {Q ell : ℕ}
    (hp : ell.Prime) (hc : ell.Coprime Q) (B d : ℕ) :
    rawPhaseProgressionMeanTerm k (Q * ell) B d =
      rawPhaseProgressionMeanTerm k Q B d +
        (if ell ∣ B then (ell : ℝ) - 1 else -1) *
          (if ell ∣ d then rawPhaseProgressionMeanTerm k Q B d else 0) := by
  rw [rawPhaseProgressionMeanTerm_eq_gcd,
    rawPhaseProgressionMeanTerm_eq_gcd, hc.symm.gcd_mul,
    rawPhaseFreshPrime_gcd hp]
  by_cases hd : ell ∣ d
  · simp only [hd, ↓reduceIte]
    have hprod : Nat.gcd d Q * ell ∣ B ↔ Nat.gcd d Q ∣ B ∧ ell ∣ B := by
      constructor
      · intro h
        exact ⟨dvd_trans (dvd_mul_right (Nat.gcd d Q) ell) h,
          dvd_trans (dvd_mul_left ell (Nat.gcd d Q)) h⟩
      · intro h
        exact (hc.symm.gcd_left d).mul_dvd_of_dvd_of_dvd h.1 h.2
    by_cases hg : Nat.gcd d Q ∣ B <;> by_cases hB : ell ∣ B <;>
      simp only [hg, hB, hprod, and_self, and_false, false_and, ↓reduceIte]
    all_goals push_cast; ring
  · simp only [hd, ↓reduceIte, Nat.mul_one, mul_zero, add_zero]

theorem summable_rawPhaseProgressionMeanTerm_multiples {k : ℕ}
    (hk : 2 ≤ k) (Q A ell : ℕ) :
    Summable (fun d : ℕ =>
      if ell ∣ d then rawPhaseProgressionMeanTerm k Q A d else 0) := by
  apply Summable.of_nonneg_of_le _ _ (summable_rawPhaseProgressionMeanTerm hk Q A)
  · intro d
    split_ifs
    · exact (rawPhaseProgressionMeanTerm_bounds hk Q A d).1
    · exact le_rfl
  · intro d
    split_ifs
    · exact le_rfl
    · exact (rawPhaseProgressionMeanTerm_bounds hk Q A d).1

theorem rawPhaseProgressionMean_congr (k : ℕ) {Q A B : ℕ}
    (hAB : Nat.ModEq Q B A) :
    rawPhaseProgressionMean k Q B = rawPhaseProgressionMean k Q A := by
  unfold rawPhaseProgressionMean
  exact tsum_congr (rawPhaseProgressionMeanTerm_congr k hAB)

theorem rawPhaseProgressionMean_refine_aux {k Q ell : ℕ}
    (hk : 2 ≤ k) (hp : ell.Prime) (hc : ell.Coprime Q) (B : ℕ) :
    rawPhaseProgressionMean k (Q * ell) B =
      (1 + (if ell ∣ B then (ell : ℝ) - 1 else -1) / (ell : ℝ) ^ (k + 1)) *
        rawPhaseProgressionMean k Q B := by
  have hs := summable_rawPhaseProgressionMeanTerm hk Q B
  have hm := summable_rawPhaseProgressionMeanTerm_multiples hk Q B ell
  calc
    _ = ∑' d : ℕ, (rawPhaseProgressionMeanTerm k Q B d +
        (if ell ∣ B then (ell : ℝ) - 1 else -1) *
          (if ell ∣ d then rawPhaseProgressionMeanTerm k Q B d else 0)) := by
      exact tsum_congr (rawPhaseProgressionMeanTerm_refine k hp hc B)
    _ = rawPhaseProgressionMean k Q B +
        (if ell ∣ B then (ell : ℝ) - 1 else -1) *
          (rawPhaseProgressionMean k Q B / (ell : ℝ) ^ (k + 1)) := by
      rw [hs.tsum_add (hm.mul_left _), tsum_mul_left,
        rawPhaseProgressionMean_multiples k hp.pos hc]
      rfl
    _ = _ := by ring

theorem rawPhaseProgressionMean_refine_no_hit {k Q A B ell : ℕ}
    (hk : 2 ≤ k) (hp : ell.Prime) (hc : ell.Coprime Q) (hAB : Nat.ModEq Q B A)
    (hB : ¬ ell ∣ B) :
    rawPhaseProgressionMean k (Q * ell) B =
      (1 - 1 / (ell : ℝ) ^ (k + 1)) * rawPhaseProgressionMean k Q A := by
  rw [rawPhaseProgressionMean_refine_aux hk hp hc, if_neg hB,
    rawPhaseProgressionMean_congr k hAB]
  ring

theorem rawPhaseProgressionMean_refine_hit {k Q A B ell : ℕ}
    (hk : 2 ≤ k) (hp : ell.Prime) (hc : ell.Coprime Q) (hAB : Nat.ModEq Q B A)
    (hB : ell ∣ B) :
    rawPhaseProgressionMean k (Q * ell) B =
      (1 + ((ell : ℝ) - 1) / (ell : ℝ) ^ (k + 1)) * rawPhaseProgressionMean k Q A := by
  rw [rawPhaseProgressionMean_refine_aux hk hp hc, if_pos hB,
    rawPhaseProgressionMean_congr k hAB]

theorem rawPhaseProgressionMean_refine {k Q A B ell : ℕ}
    (hk : 2 ≤ k) (hp : ell.Prime) (hc : ell.Coprime Q) (hAB : Nat.ModEq Q B A) :
    rawPhaseProgressionMean k (Q * ell) B =
      rawPhaseProgressionMean k Q A *
        (1 - 1 / (ell : ℝ) ^ (k + 1) + if ell ∣ B then 1 / (ell : ℝ) ^ k else 0) := by
  have he : (ell : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  by_cases hB : ell ∣ B
  · rw [rawPhaseProgressionMean_refine_hit hk hp hc hAB hB, if_pos hB, pow_succ]
    field_simp
    ring
  · rw [rawPhaseProgressionMean_refine_no_hit hk hp hc hAB hB, if_neg hB]
    ring

#print axioms rawPhaseProgressionMeanTerm_mul
#print axioms rawPhaseProgressionMean_multiples
#print axioms rawPhaseProgressionMeanTerm_congr
#print axioms rawPhaseProgressionMeanTerm_refine
#print axioms summable_rawPhaseProgressionMeanTerm_multiples
#print axioms rawPhaseProgressionMean_congr
#print axioms rawPhaseProgressionMean_refine_aux
#print axioms rawPhaseProgressionMean_refine_no_hit
#print axioms rawPhaseProgressionMean_refine_hit
#print axioms rawPhaseProgressionMean_refine

end

end Erdos252
