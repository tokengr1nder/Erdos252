import Generalizations.WeightedTail

/-!
# Stability under a convergent first-order tail perturbation

The fresh-prime contradiction excludes every constant limit, not just zero.
Consequently the scaled error may converge to any real constant. This is the
additional room needed for polynomial and exponential perturbations of E252.
-/

namespace Erdos252.Generalizations

open Filter
open scoped BigOperators Topology ArithmeticFunction.sigma

noncomputable section

theorem isolated_shift_not_tendsto_const {k : ℕ} (hk : 0 < k)
    {ι : Type*} [Fintype ι] (r : ι → ℕ) (c : ι → ℝ) (i₀ : ι) (Q A : ℕ)
    (hQ : 0 < Q) (hrpos : ∀ i, 0 < r i)
    (hunique : ∀ i, r i = r i₀ → i = i₀) (hc : c i₀ ≠ 0) (ℓ : ℝ) :
    ¬ Tendsto (fun n : ℕ => ∑ i, c i * phase k (Q * n + A + r i)) atTop (𝓝 ℓ) := by
  classical
  obtain ⟨L, hp, hcop, v₀, v₁, hmiss, hhit⟩ := fresh_prime_residues r i₀ Q A hQ hrpos
  have hLR : (0 : ℝ) < L := by exact_mod_cast hp.pos
  intro hz
  have hmean (v : ℕ) (i : ι) : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, phase k (Q * (L * n + v) + A + r i)) / (N : ℝ)) atTop
      (𝓝 (progMean k Q (A + r i) *
        (1 - 1 / (L : ℝ) ^ (k + 1) + if L ∣ Q * v + A + r i then 1 / (L : ℝ) ^ k else 0))) := by
    have hh := tendsto_progMean hk (Nat.mul_pos hQ hp.pos)
      (by have := hrpos i; omega : 0 < Q * v + (A + r i))
    rw [progMean_refine (A := A + r i) hk hQ hp hcop.symm (by simp [Nat.ModEq])] at hh
    simpa only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] using hh
  have heq (v : ℕ) := tendsto_nhds_unique (tendsto_weightedCesaro _ c _ (hmean v))
    (by simpa only [div_eq_mul_inv, mul_comm, Function.comp_def, id_eq] using
      (hz.comp ((tendsto_add_atTop_nat v).comp (tendsto_id.const_mul_atTop' hp.pos))).cesaro)
  have h₀ := heq v₀
  have h₁ := heq v₁
  simp only [hmiss, hhit, ↓reduceIte, add_zero] at h₀ h₁
  have hr (i : ι) : r i = r i₀ ↔ i = i₀ := ⟨hunique i, fun h => h ▸ rfl⟩
  simp_rw [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, hr, h₀] at h₁
  have hdiff : c i₀ * progMean k Q (A + r i₀) * (1 / (L : ℝ) ^ k) = 0 := by
    have he : ℓ + c i₀ * progMean k Q (A + r i₀) * (1 / (L : ℝ) ^ k) = ℓ := by
      simpa [mul_assoc] using h₁
    linarith
  refine (mul_ne_zero (mul_ne_zero hc (lt_of_lt_of_le one_pos ?_).ne') (by positivity)) hdiff
  simpa [progMean, meanTerm] using
    (summable_meanTerm hk hQ (A + r i₀)).le_tsum 1 fun d _ => (meanTerm_bounds hQ _ d).1

theorem weighted_raw_not_tendsto_const {k : ℕ} (hk : 0 < k) (w : ℕ → ℝ)
    (hw : w k ≠ 0) (Q A : ℕ) (hQ : 0 < Q) (ℓ : ℝ) :
    ¬ Tendsto (fun n : ℕ => weightedRaw k w (Q * n + A)) atTop (𝓝 ℓ) := by
  let i₀ : GridTerm k := ⟨gridZero k, Fin.last k⟩
  have hunique (i : GridTerm k)
      (hi : gridShift k i.1 i.2 = gridShift k i₀.1 i₀.2) : i = i₀ := by
    obtain ⟨he, hj⟩ := (gridShift_eq_succ_base_iff i.1 (Nat.lt_succ_iff.mp i.2.isLt)).mp
      (hi.trans ((gridShift_eq_succ_base_iff i₀.1 le_rfl).mpr ⟨rfl, rfl⟩))
    exact Prod.ext he (Fin.ext hj)
  simpa only [Fintype.sum_prod_type, weightedRaw, ← Fin.sum_univ_eq_sum_range] using
    isolated_shift_not_tendsto_const hk (fun i : GridTerm k => gridShift k i.1 i.2)
      (fun i : GridTerm k => w i.2 * gridCoeff k i.1 i.2) i₀ Q A hQ
      (fun i => gridShift_pos k i.1 i.2) hunique (by
        simp [i₀, gridCoeff, gridWeight, gridZero, cubeWeight, diffWeight, hw,
          Nat.stirlingSecond_self, (gridMult_pos k (gridZero k)).ne']) ℓ

theorem gridCombine_error_const (k A : ℕ) (hA : GridCongruences k A)
    (E : ℕ → ℝ) (ℓ : ℝ) (hE : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * E n) atTop (𝓝 ℓ)) :
    Tendsto (fun t : ℕ => ((A + gridModulus k * t : ℕ) : ℝ) *
      gridCombine k E (A + gridModulus k * t)) atTop
      (𝓝 (∑ e : GridVertex k,
        (gridWeight k e : ℝ) * (σ k (gridMult k e) : ℝ) * ((gridMult k e : ℝ) * ℓ))) := by
  have hE0 : Tendsto E atTop (𝓝 0) := by
    simpa only [mul_div_cancel_left₀ _ (Nat.cast_add_one_ne_zero (R := ℝ) _)] using
      hE.div_atTop (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  have he (e : GridVertex k) : Tendsto (fun t : ℕ =>
      ((A + gridModulus k * t : ℕ) : ℝ) * E (tailIndex k (A + gridModulus k * t) e))
      atTop (𝓝 ((gridMult k e : ℝ) * ℓ)) := by
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
  simpa only [gridCombine, Finset.mul_sum, mul_left_comm, mul_assoc] using
    tendsto_finsetSum Finset.univ fun e _ =>
      (he e).const_mul ((gridWeight k e : ℝ) * (σ k (gridMult k e) : ℝ))

/-- Unlike the original zero-error form, any convergent scaled error is allowed. -/
theorem weighted_tail_obstruction_of_limit {k : ℕ} (hk : 0 < k) (w T E : ℕ → ℝ)
    (hw : w k ≠ 0) (hT : ∀ n, T n = weightedExpansion k w n + E n)
    (ℓ : ℝ) (hE : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * E n) atTop (𝓝 ℓ)) :
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
  have hmain := (gridCombine_error_const k A hA E ℓ hE).neg.congr'
    (show (fun t : ℕ => -(((A + gridModulus k * t : ℕ) : ℝ) *
      gridCombine k E (A + gridModulus k * t))) =ᶠ[atTop]
      (fun t => ((A + gridModulus k * t : ℕ) : ℝ) *
        weightedReduced k w (A + gridModulus k * t)) from by
      filter_upwards [hz, heq] with t ht heq
      rw [← heq, eq_neg_of_add_eq_zero_left ((hsplit _).symm.trans ht), mul_neg])
  have hraw := hmain.sub ((weighted_rescaling k w).comp hP)
  simp only [Function.comp_apply, sub_sub_cancel, sub_zero] at hraw
  exact weighted_raw_not_tendsto_const hk w hw _ A (gridModulus_pos k) _
    (by simpa only [Nat.add_comm] using hraw)

end

end Erdos252.Generalizations
