/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Example_6_2.DiffusionMatrices

public section

namespace OneDimensionalDiffusion

/-- Helper for Exercise 6.5: left multiplication by `Matrix.diagonal κ` weights the two
nonzero entries in a column of `differenceMatrix`. -/
theorem weightedDifference_apply
    (n : ℕ) (κ : Fin (n + 1) → ℝ) (k : Fin (n + 1)) (j : Fin n) :
    (Matrix.diagonal κ * differenceMatrix n) k j =
      if k = j.castSucc then
        κ k
      else if k = j.succ then
        -κ k
      else
        0 := by
  -- A diagonal matrix rescales row `k` of `differenceMatrix` by the weight `κ k`.
  rw [Matrix.diagonal_mul]
  simp [differenceMatrix_apply]

/-- Helper for Exercise 6.5: a weighted Gram entry is the difference of the two weighted
column values adjacent to the row index. -/
theorem stiffnessGram_apply_as_columnDifference
    (n : ℕ) (κ : Fin (n + 1) → ℝ) (i j : Fin n) :
    (Matrix.transpose (differenceMatrix n) * Matrix.diagonal κ * differenceMatrix n) i j =
      (Matrix.diagonal κ * differenceMatrix n) i.castSucc j -
        (Matrix.diagonal κ * differenceMatrix n) i.succ j := by
  -- Reassociate so that `differenceMatrixᵀ` acts on the weighted `j`th column.
  rw [Matrix.mul_assoc]
  -- The owner API already computes this transpose action as a two-point difference.
  simpa [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum] using
    (differenceMatrixTranspose_mulVec_apply n
      (fun k ↦ (Matrix.diagonal κ * differenceMatrix n) k j) i)

/-- Helper for Exercise 6.5: the upper- and lower-neighbor relations on `Fin n` are mutually
exclusive. -/
theorem lowerNeighbor_ne_of_upperNeighbor
    {n : ℕ} {i j : Fin n} (h_upper : i.succ = j.castSucc) :
    j.succ ≠ i.castSucc := by
  -- Converting both neighbor equalities to statements on `Fin.val` produces an impossible cycle.
  intro h_lower
  have h_upper_val : i.1 + 1 = j.1 := by
    simpa using congrArg Fin.val h_upper
  have h_lower_val : j.1 + 1 = i.1 := by
    simpa using congrArg Fin.val h_lower
  omega

/-- Exercise 6.5. The finite-difference discretization of
`-d/dx (κ(x) * d/dx)` gives the tridiagonal stiffness matrix `(6.23)` with
prefactor `1 / h = n + 1`. -/
theorem stiffnessMatrix_apply (n : ℕ) (κ : Fin (n + 1) → ℝ) (i j : Fin n) :
    stiffnessMatrix n κ i j =
      (n + 1 : ℝ) *
        (if i = j then
          κ i.castSucc + κ i.succ
        else if i.succ = j.castSucc then
          -κ i.succ
        else if j.succ = i.castSucc then
          -κ j.succ
        else
          0) := by
  -- Rewrite the stiffness matrix entry into the weighted Gram entry from the owner definition.
  rw [stiffnessMatrix_eqWeightedGram, Matrix.smul_apply, stiffnessGram_apply_as_columnDifference]
  rw [weightedDifference_apply, weightedDifference_apply]
  -- The remaining work is a case split on the diagonal and the two neighboring bands.
  by_cases h_diag : i = j
  · subst j
    have h_castSucc_ne_succ : i.castSucc ≠ i.succ := by
      exact ne_of_lt Fin.castSucc_lt_succ
    have h_succ_ne_castSucc : i.succ ≠ i.castSucc := by
      intro h
      exact h_castSucc_ne_succ h.symm
    simp [h_succ_ne_castSucc]
  · by_cases h_upper : i.succ = j.castSucc
    · have h_lower : j.succ ≠ i.castSucc := lowerNeighbor_ne_of_upperNeighbor h_upper
      have h_cast_diag : i.castSucc ≠ j.castSucc := by
        intro h
        exact h_diag (Fin.castSucc_injective _ h)
      have h_succ_diag : i.succ ≠ j.succ := by
        intro h
        exact h_diag (Fin.succ_injective _ h)
      have h_cast_succ : i.castSucc ≠ j.succ := by
        intro h
        exact h_lower h.symm
      simp [h_diag, h_upper, h_cast_diag, h_cast_succ]
    · by_cases h_lower : j.succ = i.castSucc
      · have h_cast_diag : i.castSucc ≠ j.castSucc := by
          intro h
          exact h_diag (Fin.castSucc_injective _ h)
        have h_succ_diag : i.succ ≠ j.succ := by
          intro h
          exact h_diag (Fin.succ_injective _ h)
        have h_succ_cast : i.succ ≠ i.castSucc := by
          intro h
          exact (ne_of_lt Fin.castSucc_lt_succ) h.symm
        simp [h_diag, h_upper, h_lower, h_cast_diag, h_succ_cast]
      · have h_cast_diag : i.castSucc ≠ j.castSucc := by
          intro h
          exact h_diag (Fin.castSucc_injective _ h)
        have h_succ_diag : i.succ ≠ j.succ := by
          intro h
          exact h_diag (Fin.succ_injective _ h)
        have h_cast_succ : i.castSucc ≠ j.succ := by
          intro h
          exact h_lower h.symm
        simp [h_diag, h_upper, h_lower, h_cast_diag, h_succ_diag, h_cast_succ]

/-- The diagonal entries of `stiffnessMatrix` are the sums of the adjacent
conductivity samples, scaled by `n + 1`. -/
@[simp]
theorem stiffnessMatrix_apply_diag (n : ℕ) (κ : Fin (n + 1) → ℝ) (i : Fin n) :
    stiffnessMatrix n κ i i = (n + 1 : ℝ) * (κ i.castSucc + κ i.succ) := by
  -- Specializing the stencil to the diagonal removes both off-diagonal branches.
  have h_castSucc_ne_succ : i.castSucc ≠ i.succ := by
    exact ne_of_lt Fin.castSucc_lt_succ
  have h_succ_ne_castSucc : i.succ ≠ i.castSucc := by
    intro h
    exact h_castSucc_ne_succ h.symm
  simpa [h_castSucc_ne_succ, h_succ_ne_castSucc] using stiffnessMatrix_apply n κ i i

/-- The superdiagonal entries of `stiffnessMatrix` are the negative right-edge
conductivity samples, scaled by `n + 1`. -/
theorem stiffnessMatrix_apply_of_upperNeighbor
    (n : ℕ) (κ : Fin (n + 1) → ℝ) (i j : Fin n)
    (h_neighbor : i.succ = j.castSucc) :
    stiffnessMatrix n κ i j = -((n + 1 : ℝ) * κ i.succ) := by
  -- The upper-neighbor hypothesis isolates the superdiagonal branch of the stencil.
  have h_diag : i ≠ j := by
    intro h
    subst j
    exact (ne_of_lt Fin.castSucc_lt_succ) h_neighbor.symm
  have h_lower : j.succ ≠ i.castSucc := lowerNeighbor_ne_of_upperNeighbor h_neighbor
  simpa [h_diag, h_neighbor, h_lower, mul_neg, neg_mul] using stiffnessMatrix_apply n κ i j

/-- The subdiagonal entries of `stiffnessMatrix` are the negative left-edge
conductivity samples, scaled by `n + 1`. -/
theorem stiffnessMatrix_apply_of_lowerNeighbor
    (n : ℕ) (κ : Fin (n + 1) → ℝ) (i j : Fin n)
    (h_neighbor : j.succ = i.castSucc) :
    stiffnessMatrix n κ i j = -((n + 1 : ℝ) * κ j.succ) := by
  -- The lower-neighbor hypothesis isolates the subdiagonal branch of the stencil.
  have h_diag : i ≠ j := by
    intro h
    subst j
    exact (ne_of_lt Fin.castSucc_lt_succ) h_neighbor.symm
  have h_upper : i.succ ≠ j.castSucc := lowerNeighbor_ne_of_upperNeighbor h_neighbor
  simpa [h_diag, h_upper, h_neighbor, mul_neg, neg_mul] using stiffnessMatrix_apply n κ i j

/-- Entries of `stiffnessMatrix` vanish away from the diagonal and the two
nearest-neighbor bands. -/
theorem stiffnessMatrix_apply_zero_of_not_neighbor
    (n : ℕ) (κ : Fin (n + 1) → ℝ) (i j : Fin n)
    (hij : i ≠ j) (h_upper : i.succ ≠ j.castSucc)
    (h_lower : j.succ ≠ i.castSucc) :
    stiffnessMatrix n κ i j = 0 := by
  -- When all three stencil predicates are false, the matrix entry is zero.
  simpa [hij, h_upper, h_lower] using stiffnessMatrix_apply n κ i j

end OneDimensionalDiffusion
