import Erdos252.Solution

/-!
# The cancellation argument with arbitrary fixed shift weights

The leading shift need only have a nonzero weight. This separates the
arithmetic obstruction from the particular denominator expansion used to
produce it. All analytic and integrality hypotheses are explicit.
-/

namespace Erdos252.Generalizations

open Filter
open scoped BigOperators Topology ArithmeticFunction.sigma

noncomputable section

def weightedExpansion (k : ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1),
    w j * (Nat.stirlingSecond i j : ℝ) * (σ k (n + (j + 1)) : ℝ) /
      ((n + (j + 1) : ℕ) : ℝ) ^ (i + 1)

def weightedReduced (k : ℕ) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ e : GridVertex k, ∑ j ∈ Finset.range (k + 1),
    w j * gridCoeff k e j * phase k (N + gridShift k e j) /
      ((N + gridShift k e j : ℕ) : ℝ)

def weightedRaw (k : ℕ) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ e : GridVertex k, ∑ j ∈ Finset.range (k + 1),
    w j * gridCoeff k e j * phase k (N + gridShift k e j)

def gridCombine (k : ℕ) (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ e : GridVertex k, (gridWeight k e : ℝ) * (σ k (gridMult k e) : ℝ) *
    f (tailIndex k N e)

theorem weighted_grid_cancel (k N : ℕ) (w : ℕ → ℝ) :
    (∑ e : GridVertex k, (gridWeight k e : ℝ) *
      (∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1),
        w j * (Nat.stirlingSecond i j : ℝ) * (gridMult k e : ℝ) ^ (i + 1) *
          (σ k (N + gridShift k e j) : ℝ) /
            ((N + gridShift k e j : ℕ) : ℝ) ^ (i + 1))) = weightedReduced k w N := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm, Finset.sum_eq_single_of_mem k (by simp)]
  · rw [Finset.sum_comm]
    simp only [weightedReduced, gridCoeff, phase, pow_succ, div_eq_mul_inv,
      mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  · intro i hi hne
    refine Finset.sum_eq_zero fun j hj => ?_
    have hik := Finset.mem_range.mp hi
    have hjk := Finset.mem_range.mp hj
    by_cases hlt : j < k
    · have hc := congrArg ((w j * (Nat.stirlingSecond i j : ℝ)) * ·)
        (grid_core_cancel hlt (by omega : i + 1 ≤ k)
          (fun s => (σ k (N + s) : ℝ) / ((N + s : ℕ) : ℝ) ^ (i + 1)))
      simpa only [mul_zero, Finset.mul_sum, div_eq_mul_inv,
        mul_assoc, mul_comm, mul_left_comm] using hc
    · simp [Nat.stirlingSecond_eq_zero_of_lt (by omega : i < j)]

theorem gridCombine_expansion {k : ℕ} (hk : 0 < k) (w : ℕ → ℝ) (N : ℕ)
    (hN : gridBase k ≤ N) (hcong : GridCongruences k N) :
    gridCombine k (weightedExpansion k w) N = weightedReduced k w N := by
  rw [← weighted_grid_cancel]
  unfold gridCombine weightedExpansion
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_assoc]
  congr 1
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i _ => ?_
  simpa only [mul_assoc, mul_left_comm, mul_div_assoc] using
    congrArg ((w j * (Nat.stirlingSecond i j : ℝ)) * ·) (tailIndex_term_rescale hk N e
      ((gridOffset_lt_base k e).le.trans hN) (hcong e)
      (by have := Finset.mem_range.mp hj; omega) i)

theorem tendsto_weightedReduced (k : ℕ) (w : ℕ → ℝ) :
    Tendsto (weightedReduced k w) atTop (𝓝 0) := by
  unfold weightedReduced
  simpa only [weightedReduced, mul_assoc, mul_div_assoc, mul_zero, Finset.sum_const_zero]
    using tendsto_finsetSum Finset.univ fun e _ =>
      tendsto_finsetSum (Finset.range (k + 1)) fun j _ =>
        (grid_main_term_tendsto_zero k e j).const_mul (w j)

theorem weighted_rescaling (k : ℕ) (w : ℕ → ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * weightedReduced k w N - weightedRaw k w N)
      atTop (𝓝 0) := by
  have hh := tendsto_finsetSum Finset.univ fun e _ =>
    tendsto_finsetSum (Finset.range (k + 1)) fun j _ =>
      ((grid_main_term_tendsto_zero k e j).const_mul (w j)).neg.mul_const
        (gridShift k e j : ℝ)
  simp only [mul_zero, neg_zero, zero_mul, Finset.sum_const_zero] at hh
  refine hh.congr fun N => ?_
  unfold weightedReduced weightedRaw
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun j _ => ?_
  have hx : ((N + gridShift k e j : ℕ) : ℝ) ≠ 0 := by
    have := gridShift_pos k e j
    positivity
  field_simp
  push_cast
  ring

theorem weighted_raw_obstruction {k : ℕ} (hk : 0 < k) (w : ℕ → ℝ) (hw : w k ≠ 0)
    (Q A : ℕ) (hQ : 0 < Q) :
    ¬ Tendsto (fun n : ℕ => weightedRaw k w (Q * n + A)) atTop (𝓝 0) := by
  let i₀ : GridTerm k := ⟨gridZero k, Fin.last k⟩
  have hunique (i : GridTerm k)
      (hi : gridShift k i.1 i.2 = gridShift k i₀.1 i₀.2) : i = i₀ := by
    obtain ⟨he, hj⟩ := (gridShift_eq_succ_base_iff i.1 (Nat.lt_succ_iff.mp i.2.isLt)).mp
      (hi.trans ((gridShift_eq_succ_base_iff i₀.1 le_rfl).mpr ⟨rfl, rfl⟩))
    exact Prod.ext he (Fin.ext hj)
  simpa only [Fintype.sum_prod_type, weightedRaw, ← Fin.sum_univ_eq_sum_range] using
    isolated_shift_not_tendsto_zero hk (fun i : GridTerm k => gridShift k i.1 i.2)
      (fun i : GridTerm k => w i.2 * gridCoeff k i.1 i.2) i₀ Q A hQ
      (fun i => gridShift_pos k i.1 i.2) hunique (by
        simp [i₀, gridCoeff, gridWeight, gridZero, cubeWeight, diffWeight, hw,
          Nat.stirlingSecond_self, (gridMult_pos k (gridZero k)).ne'])

theorem gridCombine_integral (k : ℕ) (f : ℕ → ℝ)
    (hf : ∀ᶠ n in atTop, ∃ z : ℤ, f n = z) (A : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∃ z : ℤ, gridCombine k f (A + gridModulus k * t) = z := by
  classical
  have hint := eventually_all.mpr fun e : GridVertex k =>
    (tendsto_tailIndex k _ A (gridModulus_pos k) e).eventually hf
  filter_upwards [hint] with t ht
  choose z hz using ht
  exact ⟨∑ e : GridVertex k, gridWeight k e * (σ k (gridMult k e) : ℤ) * z e,
    by simp only [gridCombine, hz, Int.cast_sum, Int.cast_mul, Int.cast_natCast]⟩

theorem gridCombine_error_limit (k A : ℕ) (hA : GridCongruences k A) (E : ℕ → ℝ)
    (hE : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * E n) atTop (𝓝 0)) :
    Tendsto (fun t : ℕ => ((A + gridModulus k * t : ℕ) : ℝ) *
      gridCombine k E (A + gridModulus k * t)) atTop (𝓝 0) := by
  have hE0 : Tendsto E atTop (𝓝 0) := by
    simpa only [mul_div_cancel_left₀ _ (Nat.cast_add_one_ne_zero (R := ℝ) _)] using
      hE.div_atTop (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  have he (e : GridVertex k) : Tendsto (fun t : ℕ =>
      ((A + gridModulus k * t : ℕ) : ℝ) * E (tailIndex k (A + gridModulus k * t) e))
      atTop (𝓝 0) := by
    have hindex := tendsto_tailIndex k (gridModulus k) A (gridModulus_pos k) e
    have hlim := ((hE.comp hindex).const_mul (gridMult k e : ℝ)).sub
      ((hE0.comp hindex).const_mul (gridShift k e 0 : ℝ))
    simp only [mul_zero, sub_zero, Function.comp_apply] at hlim
    refine hlim.congr' ?_
    filter_upwards [(tendsto_affine_atTop _ A (gridModulus_pos k)).eventually
      (eventually_ge_atTop (gridOffset k e))] with t hN
    have h : (gridMult k e : ℝ) * ((tailIndex k (A + gridModulus k * t) e : ℝ) + 1) =
        ((A + gridModulus k * t : ℕ) : ℝ) + gridShift k e 0 := by
      exact_mod_cast tailIndex_factorization k _ e hN
        (gridCongruences_add_modulus_mul k A t hA e) 0
    rw [← mul_assoc, h]
    ring
  simpa only [gridCombine, Finset.mul_sum, mul_left_comm, mul_assoc, mul_zero,
    Finset.sum_const_zero] using tendsto_finsetSum Finset.univ fun e _ =>
      (he e).const_mul ((gridWeight k e : ℝ) * (σ k (gridMult k e) : ℝ))

/-- The full cancellation/mean contradiction works for arbitrary fixed shift
weights, provided the final weight is nonzero and the error is `o(1/n)`. -/
theorem weighted_tail_obstruction {k : ℕ} (hk : 0 < k) (w T E : ℕ → ℝ)
    (hw : w k ≠ 0) (hT : ∀ n, T n = weightedExpansion k w n + E n)
    (hE : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * E n) atTop (𝓝 0)) :
    ¬ (∀ᶠ n in atTop, ∃ z : ℤ, T n = z) := by
  classical
  intro hint
  obtain ⟨A, hA⟩ : ∃ N0, GridCongruences k N0 := ⟨_, fun e =>
    (Nat.chineseRemainderOfFinset (gridOffset k) (fun e => (gridMult k e) ^ 2) Finset.univ
      (fun e _ => (pow_pos (gridMult_pos k e) 2).ne')
      (fun e _ f _ hef => ((gridMult_pairwise_coprime k hef).pow_left 2).pow_right 2)).property e
      (Finset.mem_univ e)⟩
  have hP := tendsto_affine_atTop _ A (gridModulus_pos k)
  have hsplit (N : ℕ) : gridCombine k T N =
      gridCombine k (weightedExpansion k w) N + gridCombine k E N := by
    simp only [gridCombine, hT, mul_add, Finset.sum_add_distrib]
  have heq := (hP.eventually (eventually_ge_atTop (gridBase k))).mono fun t ht =>
    gridCombine_expansion hk w _ ht (gridCongruences_add_modulus_mul k A t hA)
  have hE0 : Tendsto E atTop (𝓝 0) := by
    simpa only [mul_div_cancel_left₀ _ (Nat.cast_add_one_ne_zero (R := ℝ) _)] using
      hE.div_atTop (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hEW : Tendsto (fun t : ℕ => gridCombine k E (A + gridModulus k * t))
      atTop (𝓝 0) := by
    simpa only [gridCombine, Function.comp_apply, mul_zero, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ fun e _ =>
        (hE0.comp (tendsto_tailIndex k _ A (gridModulus_pos k) e)).const_mul
          ((gridWeight k e : ℝ) * (σ k (gridMult k e) : ℝ))
  have hTW : Tendsto (fun t : ℕ => gridCombine k T (A + gridModulus k * t))
      atTop (𝓝 0) := by
    simpa only [← hsplit, add_zero] using
      (((tendsto_weightedReduced k w).comp hP).congr' (EventuallyEq.symm heq)).add hEW
  have hz := eventually_zero_of_int hTW (gridCombine_integral k T hint A)
  have hmain : Tendsto (fun t : ℕ => ((A + gridModulus k * t : ℕ) : ℝ) *
      weightedReduced k w (A + gridModulus k * t)) atTop (𝓝 0) := by
    rw [← neg_zero]
    refine (gridCombine_error_limit k A hA E hE).neg.congr' ?_
    filter_upwards [hz, heq] with t ht heq
    rw [← heq, eq_neg_of_add_eq_zero_left ((hsplit _).symm.trans ht), mul_neg]
  have hraw := hmain.sub ((weighted_rescaling k w).comp hP)
  simp only [Function.comp_apply, sub_sub_cancel, sub_zero] at hraw
  exact weighted_raw_obstruction hk w hw _ A (gridModulus_pos k)
    (by simpa only [Nat.add_comm] using hraw)

end

end Erdos252.Generalizations
