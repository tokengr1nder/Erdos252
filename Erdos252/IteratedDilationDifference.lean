import Erdos252.DilationDifference

/-!
# Arbitrarily many commuting symbolic-order dilation differences

Every finite list of directions is supported. A direction killing a core
may occur anywhere in the list, because the difference operators commute.
-/

namespace Erdos252

def iteratedDilationDifference (order : ℕ) (directions : List (ℚ × ℚ))
    (F : ℚ → ℚ → ℚ) : ℚ → ℚ → ℚ :=
  directions.foldr (fun jd G => dilationDifference order jd.1 jd.2 G) F

theorem iteratedDilationDifference_zero (order : ℕ) (directions : List (ℚ × ℚ)) :
    iteratedDilationDifference order directions (fun _ _ => 0) = (fun _ _ => 0) := by
  induction directions with
  | nil => rfl
  | cons jd directions ih =>
      simp only [iteratedDilationDifference, List.foldr_cons] at ih ⊢
      funext p t
      simp [ih, dilationDifference]

theorem iteratedDilationDifference_comm_single (order otherOrder : ℕ)
    (directions : List (ℚ × ℚ)) (j d : ℚ) (F : ℚ → ℚ → ℚ) :
    iteratedDilationDifference order directions (dilationDifference otherOrder j d F) =
      dilationDifference otherOrder j d (iteratedDilationDifference order directions F) := by
  induction directions with
  | nil => rfl
  | cons he directions ih =>
      change dilationDifference order he.1 he.2
        (iteratedDilationDifference order directions (dilationDifference otherOrder j d F)) = _
      rw [ih]
      funext p t
      exact dilationDifference_comm order otherOrder he.1 he.2 j d
        (iteratedDilationDifference order directions F) p t

/-- Any included annihilating direction kills the whole finite iteration. -/
theorem iteratedDilationDifference_eq_zero_of_mem (order : ℕ)
    {directions : List (ℚ × ℚ)} {j d : ℚ} (hmem : (j, d) ∈ directions)
    (F : ℚ → ℚ → ℚ) (hzero : dilationDifference order j d F = (fun _ _ => 0)) :
    iteratedDilationDifference order directions F = (fun _ _ => 0) := by
  induction directions with
  | nil => simp at hmem
  | cons he directions ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst he
        change dilationDifference order j d (iteratedDilationDifference order directions F) = _
        rw [← iteratedDilationDifference_comm_single, hzero,
          iteratedDilationDifference_zero]
      · change dilationDifference order he.1 he.2 (iteratedDilationDifference order directions F) = _
        funext p t
        simp [ih htail, dilationDifference]

/-- A matching direction kills all powers below an arbitrary symbolic order. -/
theorem iteratedDilationDifference_core {order ell : ℕ}
    {directions : List (ℚ × ℚ)} {j d : ℚ}
    (hmem : (j, d) ∈ directions) (hell : ell < order) (g : ℚ → ℚ) :
    iteratedDilationDifference order directions
      (fun p t => p ^ ell * g (j * p - t)) = (fun _ _ => 0) := by
  apply iteratedDilationDifference_eq_zero_of_mem order hmem
  funext p t
  exact dilationDifference_core hell j d g p t

/-- In particular, order `k+1` kills every retained degree at most `k`. -/
theorem iteratedDilationDifference_core_succ {k ell : ℕ}
    {directions : List (ℚ × ℚ)} {j d : ℚ}
    (hmem : (j, d) ∈ directions) (hell : ell ≤ k) (g : ℚ → ℚ) :
    iteratedDilationDifference (k + 1) directions
      (fun p t => p ^ ell * g (j * p - t)) = (fun _ _ => 0) := by
  exact iteratedDilationDifference_core hmem (Nat.lt_succ_of_le hell) g

#print axioms iteratedDilationDifference_zero
#print axioms iteratedDilationDifference_comm_single
#print axioms iteratedDilationDifference_eq_zero_of_mem
#print axioms iteratedDilationDifference_core
#print axioms iteratedDilationDifference_core_succ

end Erdos252
