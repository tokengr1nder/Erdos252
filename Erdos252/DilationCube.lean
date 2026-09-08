import Erdos252.IteratedDilationDifference

/-!
# Symbolic-order differences expanded over an arbitrary-dimensional cube

The difference order and cube dimension are independent parameters. Both
rational and integer versions of the actual signed product weights are
provided, with exact agreement under the rational cast.
-/

namespace Erdos252

open scoped BigOperators

def dilationCubeWeight (order : ℕ) {n : ℕ} (e : Fin n → Fin (order + 1)) : ℚ :=
  ∏ j : Fin n, dilationDifferenceWeight order (e j)

def dilationCubeWeightInt (order : ℕ) {n : ℕ} (e : Fin n → Fin (order + 1)) : ℤ :=
  ∏ j : Fin n, (-1 : ℤ) ^ (order - (e j).val) * (Nat.choose order (e j).val : ℤ)

theorem dilationCubeWeightInt_rat (order : ℕ) {n : ℕ} (e : Fin n → Fin (order + 1)) :
    (dilationCubeWeightInt order e : ℚ) = dilationCubeWeight order e := by
  simp [dilationCubeWeightInt, dilationCubeWeight, dilationDifferenceWeight]

theorem dilationCubeWeightInt_zero_ne_zero (order n : ℕ) :
    dilationCubeWeightInt order (fun _ : Fin n => (0 : Fin (order + 1))) ≠ 0 := by
  simp [dilationCubeWeightInt]

private theorem sum_dilation_cube_succ (order : ℕ) {n : ℕ}
    (G : (Fin (n + 1) → Fin (order + 1)) → ℚ) :
    (∑ e : Fin (n + 1) → Fin (order + 1), G e) =
      ∑ a : Fin (order + 1), ∑ e : Fin n → Fin (order + 1), G (Fin.cons a e) := by
  simpa only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk] using
    ((Fin.consEquiv (fun _ : Fin (n + 1) => Fin (order + 1))).sum_comp G).symm

/-- Exact expansion of symbolic-order tilted differences over the full cube. -/
theorem iteratedDilationDifference_eq_cube (order : ℕ) {n : ℕ}
    (j d : Fin n → ℚ) (F : ℚ → ℚ → ℚ) (p t : ℚ) :
    iteratedDilationDifference order (List.ofFn (fun i => (j i, d i))) F p t =
      ∑ e : Fin n → Fin (order + 1), dilationCubeWeight order e *
        F (p + ∑ i : Fin n, d i * (e i : ℕ))
          (t + ∑ i : Fin n, j i * d i * (e i : ℕ)) := by
  induction n generalizing p t with
  | zero => simp [iteratedDilationDifference, dilationCubeWeight]
  | succ n ih =>
      rw [List.ofFn_succ]
      change dilationDifference order (j 0) (d 0)
        (iteratedDilationDifference order
          (List.ofFn (fun i : Fin n => (j i.succ, d i.succ))) F) p t = _
      unfold dilationDifference
      simp_rw [ih (fun i : Fin n => j i.succ) (fun i : Fin n => d i.succ)]
      rw [sum_dilation_cube_succ]
      simp_rw [Finset.mul_sum]
      simp only [dilationCubeWeight, Fin.prod_univ_succ, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ, add_assoc, mul_assoc]

/-- A matching coordinate kills each core of degree below the symbolic order. -/
theorem dilationCube_core {order n ell : ℕ}
    (j d : Fin n → ℚ) (i : Fin n) (hell : ell < order)
    (g : ℚ → ℚ) (p t : ℚ) :
    (∑ e : Fin n → Fin (order + 1), dilationCubeWeight order e *
      ((p + ∑ a : Fin n, d a * (e a : ℕ)) ^ ell *
        g (j i * (p + ∑ a : Fin n, d a * (e a : ℕ)) -
          (t + ∑ a : Fin n, j a * d a * (e a : ℕ))))) = 0 := by
  rw [← iteratedDilationDifference_eq_cube order j d
    (fun p t => p ^ ell * g (j i * p - t)) p t]
  rw [iteratedDilationDifference_core (List.mem_ofFn.mpr ⟨i, rfl⟩) hell g]

#print axioms dilationCubeWeightInt_rat
#print axioms dilationCubeWeightInt_zero_ne_zero
#print axioms iteratedDilationDifference_eq_cube
#print axioms dilationCube_core

end Erdos252
