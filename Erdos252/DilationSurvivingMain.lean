import Erdos252.FactorialTail
import Erdos252.ProgressionMean
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Nat.ChineseRemainder

/-!
# The dilation grid, the final-order survivor, and the forced zero limit

The dimension `k`, radix `k+2`, factorial spacing and all grid coordinates
remain symbolic; the grid has pairwise coprime multipliers, positive shifts,
an isolated final shift at the zero vertex and compatible squared-modulus
congruences. Signed binomial cube weights cancel every shifted core of degree
at most `k`, leaving a weighted reciprocal-shift sum of the normalized divisor
phase. Eventual integrality of the weighted tail then forces that survivor to
vanish along one CRT progression.
-/

namespace Erdos252

open Filter
open scoped BigOperators Topology ArithmeticFunction.sigma

noncomputable section

/-- The signed binomial row for a forward difference of arbitrary order. -/
def diffWeight (order : ℕ) (i : Fin (order + 1)) : ℤ :=
  (-1) ^ (order - (i : ℕ)) * Nat.choose order (i : ℕ)

/-- All polynomial moments below the difference order vanish. -/
theorem diffWeight_moment {order ell : ℕ} (hell : ell < order) (z d : ℝ) :
    (∑ i : Fin (order + 1), (diffWeight order i : ℝ) * (z + d * (i : ℕ)) ^ ell) = 0 := by
  have hh := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
    (P := (Polynomial.C d * Polynomial.X + Polynomial.C z) ^ ell) (n := order)
    ((Polynomial.natDegree_pow_le_of_le ell Polynomial.natDegree_linear_le).trans_lt (by omega))) 0
  rw [fwdDiff_iter_eq_sum_shift, Finset.sum_range] at hh
  simpa [diffWeight, add_comm] using hh

/-- The product weight of one cube vertex. -/
def cubeWeight (order : ℕ) {n : ℕ} (e : Fin n → Fin (order + 1)) : ℤ :=
  ∏ j : Fin n, diffWeight order (e j)

theorem cubeWeight_cons (order : ℕ) {n : ℕ} (a : Fin (order + 1)) (e : Fin n → Fin (order + 1)) :
    cubeWeight order (Fin.cons a e) = diffWeight order a * cubeWeight order e := by
  simp [cubeWeight, Fin.prod_univ_succ]

private theorem sum_cube_succ (order : ℕ) {n : ℕ} (G : (Fin (n + 1) → Fin (order + 1)) → ℝ) :
    (∑ e : Fin (n + 1) → Fin (order + 1), G e) =
      ∑ a : Fin (order + 1), ∑ e : Fin n → Fin (order + 1), G (Fin.cons a e) := by
  simpa only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk] using
    ((Fin.consEquiv (fun _ : Fin (n + 1) => Fin (order + 1))).sum_comp G).symm

/-- A coordinate absent from the test argument kills every core of degree
below the difference order. -/
theorem cube_core {order ell : ℕ} (hell : ell < order) {n : ℕ}
    (d c : Fin n → ℝ) (i : Fin n) (hc : c i = 0) (g : ℝ → ℝ) (p q : ℝ) :
    (∑ e : Fin n → Fin (order + 1), (cubeWeight order e : ℝ) *
      ((p + ∑ a, d a * (e a : ℕ)) ^ ell * g (q + ∑ a, c a * (e a : ℕ)))) = 0 := by
  induction n generalizing p q with
  | zero => exact i.elim0
  | succ n ih =>
    rw [sum_cube_succ]
    simp only [cubeWeight_cons, Int.cast_mul, Fin.sum_univ_succ (n := n),
      Fin.cons_zero, Fin.cons_succ, ← add_assoc]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun e _ => ?_
      have hm := congrArg (fun x : ℝ => x * ((cubeWeight order e : ℝ) *
          g (q + ∑ b : Fin n, c b.succ * (e b : ℕ))))
        (diffWeight_moment hell (p + ∑ b : Fin n, d b.succ * (e b : ℕ)) (d 0))
      simp only [hc, zero_mul, add_zero, Finset.sum_mul] at hm ⊢
      exact (Finset.sum_congr rfl fun a _ => by ring).trans hm
    · refine Finset.sum_eq_zero fun a _ => ?_
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [ih (fun b => d b.succ) (fun b => c b.succ) i hc (p + d 0 * a) (q + c 0 * a), mul_zero]

abbrev GridVertex (k : ℕ) := Fin k → Fin (k + 2)

def gridBound (k : ℕ) : ℕ := (k + 2) ^ k - 1

def gridSpacing (k : ℕ) : ℕ := (gridBound k).factorial

def gridBase (k : ℕ) : ℕ := 1 + k * gridSpacing k * gridBound k

def gridIndex (k : ℕ) (e : GridVertex k) : ℕ := ∑ j : Fin k, (e j).val * (k + 2) ^ j.val

def gridWeightedIndex (k : ℕ) (e : GridVertex k) : ℕ :=
  ∑ j : Fin k, (j.val + 1) * (e j).val * (k + 2) ^ j.val

def gridMult (k : ℕ) (e : GridVertex k) : ℕ := gridBase k + gridSpacing k * gridIndex k e

def gridOffset (k : ℕ) (e : GridVertex k) : ℕ := gridSpacing k * gridWeightedIndex k e

def gridShift (k : ℕ) (e : GridVertex k) (j : ℕ) : ℕ := (j + 1) * gridMult k e - gridOffset k e

def gridZero (k : ℕ) : GridVertex k := fun _ => 0

def gridModulus (k : ℕ) : ℕ := ∏ e : GridVertex k, (gridMult k e) ^ 2

theorem gridBound_succ_le {k : ℕ} (hk : 1 ≤ k) : k + 1 ≤ gridBound k := by
  have hh := pow_le_pow_right' (by omega : 1 ≤ k + 2) hk
  simp only [pow_one] at hh
  unfold gridBound
  omega

theorem gridSpacing_pos (k : ℕ) : 0 < gridSpacing k := Nat.factorial_pos _

theorem gridBase_pos (k : ℕ) : 0 < gridBase k := Nat.add_pos_left Nat.one_pos _

/-- Every symbolic radix index lies in the prescribed finite interval. -/
theorem gridIndex_le (k : ℕ) (e : GridVertex k) : gridIndex k e ≤ gridBound k :=
  Nat.le_sub_one_of_lt (finFunctionFinEquiv e).isLt

/-- Fixed-length radix encodings distinguish all vertices. -/
theorem gridIndex_injective (k : ℕ) : Function.Injective (gridIndex k) :=
  fun _ _ h => finFunctionFinEquiv.injective (Fin.ext h)

theorem gridIndex_zero (k : ℕ) : gridIndex k (gridZero k) = 0 := by
  simp [gridIndex, gridZero]

/-- The coordinate-weighted index is at most the dimension times the index. -/
theorem gridWeightedIndex_le (k : ℕ) (e : GridVertex k) :
    gridWeightedIndex k e ≤ k * gridIndex k e := by
  unfold gridWeightedIndex gridIndex
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  simpa only [mul_assoc] using Nat.mul_le_mul_right ((e j).val * (k + 2) ^ j.val) j.isLt

theorem gridMult_pos (k : ℕ) (e : GridVertex k) : 0 < gridMult k e :=
  Nat.add_pos_left (gridBase_pos k) _

/-- Each multiplier is one modulo the factorial spacing. -/
theorem gridMult_coprime_spacing (k : ℕ) (e : GridVertex k) :
    Nat.Coprime (gridMult k e) (gridSpacing k) := by
  simp only [gridMult, gridBase, Nat.coprime_add_mul_left_left,
    Nat.mul_right_comm k (gridSpacing k) (gridBound k),
    Nat.coprime_add_mul_right_left, Nat.coprime_one_left_eq_true]

private theorem multipliers_coprime_of_index_lt {k : ℕ} {e f : GridVertex k}
    (hef : gridIndex k e < gridIndex k f) :
    Nat.Coprime (gridMult k e) (gridMult k f) := by
  apply Nat.coprime_of_dvd
  intro l hl hle hlf
  have hlD : Nat.Coprime l (gridSpacing k) := (gridMult_coprime_spacing k e).coprime_dvd_left hle
  have hd := Nat.dvd_sub hlf hle
  simp only [gridMult, Nat.add_sub_add_left, ← Nat.mul_sub_left_distrib] at hd
  have hdiff : l ∣ gridIndex k f - gridIndex k e := hlD.dvd_mul_left.mp hd
  have hlF : l ≤ gridBound k := (Nat.le_of_dvd (Nat.sub_pos_of_lt hef) hdiff).trans
      ((Nat.sub_le _ _).trans (gridIndex_le k f))
  exact (hl.coprime_iff_not_dvd.mp hlD) (Nat.dvd_factorial hl.pos hlF)

/-- The complete symbolic-dimensional grid has pairwise coprime multipliers. -/
theorem gridMult_pairwise_coprime (k : ℕ) :
    Pairwise (fun e f : GridVertex k =>
      Nat.Coprime (gridMult k e) (gridMult k f)) := by
  intro e f hef
  rcases lt_or_gt_of_ne (fun h => hef (gridIndex_injective k h)) with h | h
  · exact multipliers_coprime_of_index_lt h
  · exact (multipliers_coprime_of_index_lt h).symm

/-- Every offset is smaller than the base multiplier. -/
theorem gridOffset_lt_base (k : ℕ) (e : GridVertex k) : gridOffset k e < gridBase k := by
  have hDW := Nat.mul_le_mul_left (gridSpacing k) (gridWeightedIndex_le k e)
  have hDI := Nat.mul_le_mul_left (gridSpacing k * k) (gridIndex_le k e)
  unfold gridOffset gridBase
  nlinarith

theorem gridShift_pos (k : ℕ) (e : GridVertex k) (j : ℕ) : 0 < gridShift k e j :=
  Nat.sub_pos_of_lt ((gridOffset_lt_base k e).trans_le
    ((Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_left _ j.succ_pos)))

/-- Natural subtraction in the shift expression is exact. -/
theorem gridShift_add_offset (k : ℕ) (e : GridVertex k) (j : ℕ) :
    gridShift k e j + gridOffset k e = (j + 1) * gridMult k e := by
  have hp := gridShift_pos k e j
  unfold gridShift at hp ⊢
  omega

/-- Among all vertices and all orders at most `k`, the distinguished shift
`(k+1) * base` occurs exactly once: at the zero vertex and the final order. -/
theorem gridShift_eq_succ_base_iff {k : ℕ} (e : GridVertex k) {j : ℕ} (hj : j ≤ k) :
    gridShift k e j = (k + 1) * gridBase k ↔ e = gridZero k ∧ j = k := by
  have hs := gridShift_add_offset k e j
  have hW := Nat.mul_le_mul_left (gridSpacing k) (gridWeightedIndex_le k e)
  have hI := Nat.mul_le_mul_left (gridSpacing k * k) (gridIndex_le k e)
  constructor
  · intro he
    rw [he] at hs
    unfold gridOffset gridMult gridBase at hs
    have hjk : j = k := by
      by_contra hne
      have hlt : j + 1 ≤ k := by omega
      have hmul := Nat.mul_le_mul_right
        (1 + k * gridSpacing k * gridBound k + gridSpacing k * gridIndex k e) hlt
      nlinarith
    rw [hjk] at hs
    refine ⟨gridIndex_injective k ?_, hjk⟩
    rw [gridIndex_zero]
    exact (Nat.mul_eq_zero.mp
      (by nlinarith : gridSpacing k * gridIndex k e = 0)).resolve_left (gridSpacing_pos k).ne'
  · rintro ⟨rfl, rfl⟩
    simp [gridShift, gridMult, gridOffset, gridIndex, gridWeightedIndex, gridZero]

theorem gridModulus_pos (k : ℕ) : 0 < gridModulus k :=
  Finset.prod_pos (fun e _ => pow_pos (gridMult_pos k e) 2)

/-- All prescribed offset congruences have a simultaneous squared-modulus solution. -/
theorem grid_exists_crt (k : ℕ) :
    ∃ N0 : ℕ, ∀ e : GridVertex k, N0 ≡ gridOffset k e [MOD (gridMult k e) ^ 2] := by
  classical
  let N0 := Nat.chineseRemainderOfFinset (gridOffset k)
    (fun e => (gridMult k e) ^ 2) Finset.univ
    (fun e _ => (pow_pos (gridMult_pos k e) 2).ne')
    (fun e _ f _ hef => ((gridMult_pairwise_coprime k hef).pow_left 2).pow_right 2)
  exact ⟨N0, fun e => N0.property e (Finset.mem_univ e)⟩

def gridWeight (k : ℕ) (e : GridVertex k) : ℤ := cubeWeight (k + 1) e

theorem gridWeight_zero_ne_zero (k : ℕ) : gridWeight k (gridZero k) ≠ 0 := by
  simp [gridWeight, gridZero, cubeWeight, diffWeight]

theorem gridMult_real_eq_cube (k : ℕ) (e : GridVertex k) : (gridMult k e : ℝ) = (gridBase k : ℝ) +
      ∑ i : Fin k, (gridSpacing k : ℝ) * ((k : ℝ) + 2) ^ i.val * (e i).val := by
  unfold gridMult gridIndex
  push_cast
  simp only [Finset.mul_sum, mul_comm, mul_left_comm]

theorem gridShift_real_eq_cube (k : ℕ) (e : GridVertex k) (j : ℕ) :
    (gridShift k e j : ℝ) = ((j : ℝ) + 1) * gridBase k + ∑ i : Fin k, ((j : ℝ) - i.val) *
        ((gridSpacing k : ℝ) * ((k : ℝ) + 2) ^ i.val) * (e i).val := by
  rw [show (gridShift k e j : ℝ) = ((j : ℝ) + 1) * gridMult k e - gridOffset k e from
    eq_sub_of_add_eq (by exact_mod_cast gridShift_add_offset k e j), gridMult_real_eq_cube]
  unfold gridOffset gridWeightedIndex
  push_cast
  simp only [mul_add, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- All lower-order shifted cores cancel on the actual symbolic grid. -/
theorem grid_core_real_cancel {k j ell : ℕ} (hj : j < k) (hell : ell ≤ k) (g : ℝ → ℝ) :
    (∑ e : GridVertex k, (gridWeight k e : ℝ) *
      ((gridMult k e : ℝ) ^ ell * g (gridShift k e j))) = 0 := by
  simp_rw [gridMult_real_eq_cube, gridShift_real_eq_cube]
  exact cube_core (Nat.lt_succ_of_le hell)
    (fun i : Fin k => (gridSpacing k : ℝ) * ((k : ℝ) + 2) ^ i.val)
    (fun i : Fin k => ((j : ℝ) - i.val) * ((gridSpacing k : ℝ) * ((k : ℝ) + 2) ^ i.val))
    ⟨j, hj⟩ (by simp) g _ _

/-- Actual integer weights cancel every real-valued shifted core through degree `k`. -/
theorem grid_core_cancel {k j ell : ℕ} (hj : j < k) (hell : ell ≤ k) (g : ℕ → ℝ) :
    (∑ e : GridVertex k, (gridWeight k e : ℝ) *
      ((gridMult k e : ℝ) ^ ell * g (gridShift k e j))) = 0 := by
  simpa only [Nat.floor_natCast] using grid_core_real_cancel hj hell (fun z => g ⌊z⌋₊)

def gridCore (k N j i : ℕ) : ℝ := ∑ e : GridVertex k, (gridWeight k e : ℝ) *
    ((gridMult k e : ℝ) ^ (i + 1) * ((σ k (N + gridShift k e j) : ℝ) /
        ((N + gridShift k e j : ℕ) : ℝ) ^ (i + 1)))

def finiteMain (k N : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
    (Nat.stirlingSecond i j : ℝ) * gridCore k N j i

def gridCoeff (k : ℕ) (e : GridVertex k) (j : ℕ) : ℝ :=
  (gridWeight k e : ℝ) * (gridMult k e : ℝ) ^ (k + 1) * (Nat.stirlingSecond k j : ℝ)

def survivingMain (k N : ℕ) : ℝ := ∑ e : GridVertex k, ∑ j ∈ Finset.range (k + 1),
    gridCoeff k e j * phase k (N + gridShift k e j) / ((N + gridShift k e j : ℕ) : ℝ)

def survivor (k N : ℕ) : ℝ :=
  ∑ e : GridVertex k, ∑ j ∈ Finset.range (k + 1), gridCoeff k e j * phase k (N + gridShift k e j)

/-- Only the top denominator order survives: lower orders cancel on the grid,
and orders below the shift carry no Stirling coefficient. -/
theorem finiteMain_eq_final (k N : ℕ) : finiteMain k N =
      ∑ j ∈ Finset.range (k + 1), (Nat.stirlingSecond k j : ℝ) * gridCore k N j k := by
  unfold finiteMain
  rw [Finset.sum_eq_single_of_mem k (by simp)]
  · intro i hi hne
    refine Finset.sum_eq_zero fun j hj => ?_
    have hik := Finset.mem_range.mp hi
    have hjk := Finset.mem_range.mp hj
    by_cases hlt : j < k
    · rw [show gridCore k N j i = 0 from grid_core_cancel hlt (by omega)
        (fun s => (σ k (N + s) : ℝ) / ((N + s : ℕ) : ℝ) ^ (i + 1)), mul_zero]
    · rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : i < j), Nat.cast_zero, zero_mul]

/-- Exact expression of the surviving denominator order as raw phases. -/
theorem finiteMain_eq_surviving (k N : ℕ) : finiteMain k N = survivingMain k N := by
  have hdiv (x : ℕ) : (σ k x : ℝ) / (x : ℝ) ^ (k + 1) =
      phase k x / (x : ℝ) := by rw [phase, div_div, pow_succ]
  rw [finiteMain_eq_final]
  unfold gridCore survivingMain gridCoeff
  simp_rw [Finset.mul_sum, hdiv]
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- Reordering the expanded vertex sums gives the same finite main term. -/
theorem finiteMain_vertex (k N : ℕ) : finiteMain k N = ∑ e : GridVertex k, (gridWeight k e : ℝ) *
        (∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1),
          (Nat.stirlingSecond i j : ℝ) * (gridMult k e : ℝ) ^ (i + 1) *
              (σ k (N + gridShift k e j) : ℝ) / ((N + gridShift k e j : ℕ) : ℝ) ^ (i + 1)) := by
  unfold finiteMain gridCore
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- The isolated final-order coefficient never vanishes. -/
theorem gridCoeff_zero_ne_zero (k : ℕ) : gridCoeff k (gridZero k) k ≠ 0 := by
  simp only [gridCoeff, gridMult, gridIndex_zero, mul_zero, add_zero,
    Nat.stirlingSecond_self, Nat.cast_one, mul_one]
  exact mul_ne_zero (by exact_mod_cast gridWeight_zero_ne_zero k)
    (pow_ne_zero _ (by exact_mod_cast (gridBase_pos k).ne'))

/-- The raw divisor phase is sublinear even in degrees zero and one. -/
theorem tendsto_phase_div_nat (k : ℕ) :
    Tendsto (fun n : ℕ => phase k n / (n : ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => 64 * (√(n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_sqrt_div_nat.const_mul (64 : ℝ)
  refine squeeze_zero' (Eventually.of_forall fun n => by unfold phase; positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa only [phase, mul_div_assoc] using div_le_div_of_nonneg_right
    (sigma_div_le_sqrt k n (by omega)) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

/-- Every fixed coefficient and shift preserves the vanishing ratio limit. -/
theorem grid_main_term_tendsto_zero (k : ℕ) (e : GridVertex k) (h : ℕ) :
    Tendsto (fun N : ℕ =>
      gridCoeff k e h * phase k (N + gridShift k e h) /
        ((N + gridShift k e h : ℕ) : ℝ)) atTop (𝓝 0) := by
  simpa only [mul_zero, mul_div_assoc, Function.comp_apply] using ((tendsto_phase_div_nat k).comp
      (tendsto_add_atTop_nat (gridShift k e h))).const_mul (gridCoeff k e h)

/-- The complete actual surviving main term tends to zero. -/
theorem tendsto_survivingMain (k : ℕ) : Tendsto (survivingMain k) atTop (𝓝 0) := by
  unfold survivingMain
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum (Finset.univ : Finset (GridVertex k))
      (fun e _ => tendsto_finsetSum (Finset.range (k + 1))
        (fun h _ => grid_main_term_tendsto_zero k e h))

/-- Multiplying the main expression by `N` differs from the survivor by a
finite sum of vanishing terms. -/
theorem tendsto_survivor_rescaling (k : ℕ) :
    Tendsto (fun N : ℕ =>
      (N : ℝ) * survivingMain k N - survivor k N)
      atTop (𝓝 0) := by
  have hh := tendsto_finsetSum (Finset.univ : Finset (GridVertex k))
    (fun e _ => tendsto_finsetSum (Finset.range (k + 1))
      (fun h _ => (grid_main_term_tendsto_zero k e h).neg.mul_const
        (gridShift k e h : ℝ)))
  simp only [neg_zero, zero_mul, Finset.sum_const_zero] at hh
  refine hh.congr fun N => ?_
  unfold survivingMain survivor
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun h hh => ?_
  have hx : ((N + gridShift k e h : ℕ) : ℝ) ≠ 0 := by
    have := gridShift_pos k e h
    exact_mod_cast (show N + gridShift k e h ≠ 0 by omega)
  field_simp
  push_cast
  ring

theorem tendsto_affine_atTop (Q A : ℕ) (hQ : 0 < Q) :
    Tendsto (fun t : ℕ => A + Q * t) atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.le_add_left _ _) (tendsto_id.const_mul_atTop' hQ)

def tailIndex (k N : ℕ) (e : GridVertex k) : ℕ := (N - gridOffset k e) / gridMult k e

def GridCongruences (k N : ℕ) : Prop :=
  ∀ e : GridVertex k, N ≡ gridOffset k e [MOD (gridMult k e) ^ 2]

def gridThreshold (k K : ℕ) : ℕ := gridBase k + (gridBase k + gridSpacing k * gridBound k) * K

/-- Exact conversion of a shifted quotient into the common shifted argument. -/
theorem tailIndex_factorization (k N : ℕ) (e : GridVertex k) (hN : gridOffset k e ≤ N)
    (hcong : N ≡ gridOffset k e [MOD (gridMult k e) ^ 2]) (j : ℕ) :
    gridMult k e * (tailIndex k N e + (j + 1)) = N + gridShift k e j := by
  have hindex : gridMult k e * tailIndex k N e + gridOffset k e = N := by
    unfold tailIndex
    rw [Nat.mul_comm, Nat.div_mul_cancel ((dvd_pow_self _ (by norm_num : (2 : ℕ) ≠ 0)).trans
      hcong.symm.dvd'), Nat.sub_add_cancel hN]
  have hshift := gridShift_add_offset k e j
  nlinarith

/-- Every retained actual shift is coprime to the grid multiplier. -/
theorem index_coprime {k : ℕ} (hk : 0 < k) (N : ℕ) (e : GridVertex k)
    (hcong : N ≡ gridOffset k e [MOD (gridMult k e) ^ 2]) {j : ℕ} (hj : j ≤ k) :
    Nat.Coprime (gridMult k e) (tailIndex k N e + (j + 1)) := by
  rw [Nat.coprime_add_iff_right (show gridMult k e ∣ tailIndex k N e from
    Nat.dvd_div_of_mul_dvd (by simpa only [pow_two] using hcong.symm.dvd'))]
  exact (gridMult_coprime_spacing k e).coprime_dvd_right
    (Nat.dvd_factorial j.succ_pos ((by omega : j + 1 ≤ k + 1).trans (gridBound_succ_le hk)))

/-- Exact numerator and denominator rescaling for every denominator exponent. -/
theorem tailIndex_term_rescale {k : ℕ} (hk : 0 < k) (N : ℕ) (e : GridVertex k)
    (hN : gridOffset k e ≤ N) (hcong : N ≡ gridOffset k e [MOD (gridMult k e) ^ 2])
    {j : ℕ} (hj : j ≤ k) (i : ℕ) :
    (σ k (gridMult k e) : ℝ) * ((σ k (tailIndex k N e + (j + 1)) : ℝ) /
          ((tailIndex k N e + (j + 1) : ℕ) : ℝ) ^ (i + 1)) =
      (gridMult k e : ℝ) ^ (i + 1) * (σ k (N + gridShift k e j) : ℝ) /
          ((N + gridShift k e j : ℕ) : ℝ) ^ (i + 1) := by
  have hp : (gridMult k e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (gridMult_pos k e).ne'
  rw [← tailIndex_factorization k N e hN hcong j,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (index_coprime hk N e hcong hj)]
  push_cast
  rw [mul_pow, mul_div_mul_left _ _ (pow_ne_zero (i + 1) hp), mul_div_assoc]

theorem gridThreshold_vertex_le (k K : ℕ) (e : GridVertex k) :
    gridOffset k e + gridMult k e * K ≤ gridThreshold k K := by
  exact Nat.add_le_add (gridOffset_lt_base k e).le (Nat.mul_le_mul_right K (Nat.add_le_add_left
      (Nat.mul_le_mul_left (gridSpacing k) (gridIndex_le k e)) _))

/-- One explicit threshold makes all quotient indices simultaneously large. -/
theorem tailIndex_ge (k N K : ℕ) (hN : gridThreshold k K ≤ N) (e : GridVertex k) :
    K ≤ tailIndex k N e := by
  have hv := (gridThreshold_vertex_le k K e).trans hN
  unfold tailIndex
  apply (Nat.le_div_iff_mul_le (gridMult_pos k e)).mpr
  have hmul : gridMult k e * K ≤ N - gridOffset k e := by omega
  simpa only [Nat.mul_comm] using hmul

theorem gridThreshold_offset_le (k N K : ℕ) (hN : gridThreshold k K ≤ N) (e : GridVertex k) :
    gridOffset k e ≤ N := by
  have hv := (gridThreshold_vertex_le k K e).trans hN
  omega

/-- The congruences persist along the entire CRT progression. -/
theorem gridCongruences_add_modulus_mul (k N0 t : ℕ) (hN0 : GridCongruences k N0) :
    GridCongruences k (N0 + gridModulus k * t) := by
  intro e
  simpa only [Nat.add_zero] using (hN0 e).add
      ((dvd_mul_of_dvd_left (show (gridMult k e) ^ 2 ∣ gridModulus k from
        Finset.dvd_prod_of_mem (fun f : GridVertex k => (gridMult k f) ^ 2)
          (Finset.mem_univ e)) t).modEq_zero_nat)

def weightedTail (k N : ℕ) : ℝ := ∑ e : GridVertex k, (gridWeight k e : ℝ) *
    (σ k (gridMult k e) : ℝ) * scaledTail k (tailIndex k N e + 1)

def weightedMain (k N : ℕ) : ℝ := ∑ e : GridVertex k, (gridWeight k e : ℝ) *
    (σ k (gridMult k e) : ℝ) * tailMain k (tailIndex k N e)

def weightedError (k N : ℕ) : ℝ := ∑ e : GridVertex k, (gridWeight k e : ℝ) *
    (σ k (gridMult k e) : ℝ) * tailErr k (tailIndex k N e)

theorem weightedTail_split (k N : ℕ) : weightedTail k N = weightedMain k N + weightedError k N := by
  unfold weightedTail weightedMain weightedError
  simp_rw [scaledTail_expansion, mul_add, Finset.sum_add_distrib]

theorem eventually_weightedTail_integral (k : ℕ) (hx : ¬ Irrational (alpha k)) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∃ z : ℤ, weightedTail k N = z := by
  classical
  obtain ⟨K, hK⟩ := eventually_scaledTail_integral k hx
  refine ⟨gridThreshold k K, fun N hN => ?_⟩
  choose z hz using fun e : GridVertex k => hK _ ((tailIndex_ge k N K hN e).trans (Nat.le_succ _))
  exact ⟨∑ e : GridVertex k, gridWeight k e * (σ k (gridMult k e) : ℤ) * z e,
    by simp only [weightedTail, hz, Int.cast_sum, Int.cast_mul, Int.cast_natCast]⟩

theorem eventually_weightedTail_integral_prog (k : ℕ) (hx : ¬ Irrational (alpha k)) (A : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∃ z : ℤ, weightedTail k (A + gridModulus k * t) = z := by
  obtain ⟨T, hT⟩ := eventually_weightedTail_integral k hx
  exact (tendsto_affine_atTop _ A (gridModulus_pos k)).eventually ((eventually_ge_atTop T).mono hT)

/-- Every actual quotient index tends to infinity on a positive-step progression. -/
theorem tendsto_tailIndex (k Q A : ℕ) (hQ : 0 < Q) (e : GridVertex k) :
    Tendsto (fun t : ℕ => tailIndex k (A + Q * t) e) atTop atTop :=
  (Nat.tendsto_div_const_atTop (gridMult_pos k e).ne').comp
    ((tendsto_sub_atTop_nat (gridOffset k e)).comp (tendsto_affine_atTop Q A hQ))

/-- Cancellation identifies the actual weighted main term with the actual survivor main term. -/
theorem weightedMain_eq_surviving {k : ℕ} (hk : 0 < k) (N : ℕ)
    (hN : gridThreshold k 0 ≤ N) (hcong : GridCongruences k N) :
    weightedMain k N = survivingMain k N := by
  rw [← finiteMain_eq_surviving, finiteMain_vertex]
  unfold weightedMain
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_assoc, tailMain_eq_range]
  congr 1
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i _ => ?_
  simpa only [mul_assoc, mul_left_comm, mul_div_assoc] using
    congrArg ((Nat.stirlingSecond i j : ℝ) * ·) (tailIndex_term_rescale hk N e
      (gridThreshold_offset_le k N 0 hN e) (hcong e) (by have := Finset.mem_range.mp hj; omega) i)

private theorem le_progression (k A t : ℕ) : t ≤ A + gridModulus k * t :=
  (Nat.le_mul_of_pos_left t (gridModulus_pos k)).trans (Nat.le_add_left _ _)

/-- The common argument is bounded by one multiplier times its index plus one. -/
theorem tailIndex_common_le (k N : ℕ) (e : GridVertex k) (hN : gridOffset k e ≤ N)
    (hcong : N ≡ gridOffset k e [MOD (gridMult k e) ^ 2]) :
    (N : ℝ) ≤ (gridMult k e : ℝ) * ((tailIndex k N e : ℝ) + 1) := by
  have h := Nat.le_add_right N (gridShift k e 0)
  rw [← tailIndex_factorization k N e hN hcong 0] at h
  exact_mod_cast h

/-- The actual error at one CRT index stays negligible after multiplication
by the common progression argument. -/
theorem tendsto_grid_vertex_error_mul (k A : ℕ) (hA : GridCongruences k A) (e : GridVertex k) :
    Tendsto (fun t : ℕ => ((A + gridModulus k * t : ℕ) : ℝ) *
      tailErr k (tailIndex k (A + gridModulus k * t) e))
      atTop (𝓝 0) := by
  have hindex := tendsto_tailIndex k (gridModulus k) A (gridModulus_pos k) e
  have hlim : Tendsto (fun t : ℕ => (gridMult k e : ℝ) *
      (((tailIndex k (A + gridModulus k * t) e : ℝ) + 1) *
        tailErr k (tailIndex k (A + gridModulus k * t) e)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_tailErr_mul k).comp hindex).const_mul (gridMult k e : ℝ)
  have hnonneg : ∀ᶠ t : ℕ in atTop, 0 ≤ tailErr k (tailIndex k (A + gridModulus k * t) e) := by
    filter_upwards [hindex.eventually (eventually_ge_atTop (k + 1))] with t ht
    exact tailErr_nonneg k _ ht
  refine squeeze_zero' (hnonneg.mono fun t ht => mul_nonneg (Nat.cast_nonneg _) ht) ?_ hlim
  filter_upwards [hnonneg, eventually_ge_atTop (gridThreshold k 0)] with t ht hlarge
  have hN := gridThreshold_offset_le k _ 0 (hlarge.trans (le_progression k A t)) e
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (tailIndex_common_le k _ e
    hN (gridCongruences_add_modulus_mul k A t hA e)) ht

/-- Fixed signed weights preserve the vanishing scaled-error limit. -/
theorem tendsto_weightedError_mul (k A : ℕ) (hA : GridCongruences k A) :
    Tendsto (fun t : ℕ => ((A + gridModulus k * t : ℕ) : ℝ) *
      weightedError k (A + gridModulus k * t)) atTop (𝓝 0) := by
  simpa only [weightedError, Finset.mul_sum,
    mul_left_comm, mul_assoc, mul_zero, Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.univ : Finset (GridVertex k)) (fun e _ =>
      (tendsto_grid_vertex_error_mul k A hA e).const_mul
        ((gridWeight k e : ℝ) * (σ k (gridMult k e) : ℝ)))

theorem tendsto_weightedError (k A : ℕ) (hA : GridCongruences k A) :
    Tendsto (fun t : ℕ => weightedError k (A + gridModulus k * t))
      atTop (𝓝 0) := by
  have hN := (tendsto_natCast_atTop_atTop (R := ℝ)).comp
    (tendsto_affine_atTop (gridModulus k) A (gridModulus_pos k))
  refine ((tendsto_weightedError_mul k A hA).div_atTop hN).congr' ?_
  filter_upwards [hN.eventually_ne_atTop 0] with t ht
  exact mul_div_cancel_left₀ _ ht

/-- Beyond the threshold, the weighted main term is the surviving main term
along the whole CRT progression. -/
theorem eventually_main_eq_surviving {k : ℕ} (hk : 0 < k) (A : ℕ) (hA : GridCongruences k A) :
    (fun t : ℕ => weightedMain k (A + gridModulus k * t)) =ᶠ[atTop]
      fun t : ℕ => survivingMain k (A + gridModulus k * t) := by
  filter_upwards [eventually_ge_atTop (gridThreshold k 0)] with t ht
  exact weightedMain_eq_surviving hk _ (ht.trans (le_progression k A t))
    (gridCongruences_add_modulus_mul k A t hA)

theorem tendsto_weightedTail {k : ℕ} (hk : 0 < k) (A : ℕ) (hA : GridCongruences k A) :
    Tendsto (fun t : ℕ => weightedTail k (A + gridModulus k * t))
      atTop (𝓝 0) := by
  have hmain := ((tendsto_survivingMain k).comp
    (tendsto_affine_atTop _ A (gridModulus_pos k))).congr'
    (eventually_main_eq_surviving hk A hA).symm
  simpa only [← weightedTail_split, add_zero] using hmain.add (tendsto_weightedError k A hA)

/-- Rationality forces the actual generic survivor to vanish on a CRT progression. -/
theorem tendsto_survivor_of_rational {k : ℕ} (hk : 0 < k)
    (hx : ¬ Irrational (alpha k)) (A : ℕ) (hA : GridCongruences k A) :
    Tendsto (fun t : ℕ => survivor k (A + gridModulus k * t))
      atTop (𝓝 0) := by
  have hz := eventually_zero_of_int (tendsto_weightedTail hk A hA)
    (eventually_weightedTail_integral_prog k hx A)
  have hmain : Tendsto (fun t : ℕ => ((A + gridModulus k * t : ℕ) : ℝ) *
      survivingMain k (A + gridModulus k * t)) atTop (𝓝 0) := by
    rw [← neg_zero]
    refine (tendsto_weightedError_mul k A hA).neg.congr' ?_
    filter_upwards [hz, eventually_main_eq_surviving hk A hA] with t ht heq
    rw [← heq, eq_neg_of_add_eq_zero_left ((weightedTail_split k _).symm.trans ht), mul_neg]
  simpa only [Function.comp_apply, sub_sub_cancel, sub_zero] using hmain.sub
    ((tendsto_survivor_rescaling k).comp (tendsto_affine_atTop _ A (gridModulus_pos k)))

end

end Erdos252
