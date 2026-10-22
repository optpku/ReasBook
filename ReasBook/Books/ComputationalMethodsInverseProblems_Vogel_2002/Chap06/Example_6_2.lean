/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

import Mathlib.LinearAlgebra.Matrix.Action

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Example_6_2.DiffusionMatrices

public section

open OneDimensionalDiffusion

/- Example 6.2-extra-1 (1). With `h = 1 / (n + 1)`, the discrete stiffness matrix from
equation `(6.29)` is `(1 / h) Bxᵀ diag κ Bx`. -/
#check OneDimensionalDiffusion.stiffnessMatrix_eqWeightedGram

/- Example 6.2-extra-1 (2). If each conductivity sample is positive, then the stiffness matrix
from equation `(6.23)` is positive definite. -/
#check OneDimensionalDiffusion.stiffnessMatrix_posDefOfPos

/-- Example 6.2-extra-1 (3). The unweighted discrete Neumann Laplacian from equation `(6.27)`
is the Gram matrix `Bx * Bxᵀ` coming from the difference operator in equation `(6.30)`. -/
theorem neumannLaplacian_eqDifferenceMatrixMulTranspose (n : ℕ) :
    OneDimensionalDiffusion.neumannLaplacian n =
      OneDimensionalDiffusion.differenceMatrix n *
        Matrix.transpose (OneDimensionalDiffusion.differenceMatrix n) := by
  -- Re-export the core Gram identity as the item-owned main theorem.
  simpa using OneDimensionalDiffusion.neumannLaplacian_eqDifferenceMatrixMulTranspose n

/-- Corollary for Example 6.2-extra-1: with `h = 1 / (n + 1)`, the source regularization matrix
in equation `(6.27)` is `(1 / h)` times the unweighted discrete Neumann Laplacian. -/
theorem regularizationLaplacianGramFormula (n : ℕ) :
    (n + 1 : ℝ) • neumannLaplacian n =
      (n + 1 : ℝ) •
        (differenceMatrix n * Matrix.transpose (differenceMatrix n)) := by
  -- Scale the item's Gram identity by the mesh-width factor `1 / h = n + 1`.
  simpa using congrArg ((n + 1 : ℝ) • ·)
    (OneDimensionalDiffusion.neumannLaplacian_eqDifferenceMatrixMulTranspose n)

/-- Corollary for Example 6.2-extra-1: the source discrete Neumann Laplacian from equation
`(6.27)`, namely `(n + 1 : ℝ) • neumannLaplacian n`, is positive semidefinite. -/
theorem regularizationLaplacianPosSemidef (n : ℕ) :
    Matrix.PosSemidef ((n + 1 : ℝ) • neumannLaplacian n) := by
  exact (neumannLaplacian_posSemidef n).smul (add_nonneg n.cast_nonneg zero_le_one)

/-- Corollary for Example 6.2-extra-1: the null space of the source discrete Neumann Laplacian
from equation `(6.27)` consists exactly of the constant vectors, so it is spanned by
`fun _ ↦ 1`. -/
theorem regularizationLaplacian_mulVecEqZero_iffExistsConst (n : ℕ)
    (x : Fin (n + 1) → ℝ) :
    Matrix.mulVec ((n + 1 : ℝ) • neumannLaplacian n) x = 0 ↔ ∃ c : ℝ, x = fun _ ↦ c := by
  constructor
  · intro hx
    rw [Matrix.smul_mulVec] at hx
    have hx₀ : Matrix.mulVec (neumannLaplacian n) x = 0 := by
      refine (smul_eq_zero.mp hx).resolve_left ?_
      exact ne_of_gt (add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one)
    have hreachable : ∀ i j : Fin (n + 1), x i = x j := by
      have hxPath :
          Matrix.mulVec ((SimpleGraph.pathGraph (n + 1)).lapMatrix ℝ) x = 0 := by
        simpa [neumannLaplacian_eqPathGraphLapMatrix n] using hx₀
      have hpath :
          ∀ i j : Fin (n + 1),
            (SimpleGraph.pathGraph (n + 1)).Reachable i j → x i = x j :=
        ((SimpleGraph.pathGraph (n + 1)).lapMatrix_mulVec_eq_zero_iff_forall_reachable).mp hxPath
      exact fun i j ↦ hpath i j ((SimpleGraph.pathGraph_connected n).preconnected i j)
    refine ⟨x 0, funext fun i ↦ hreachable i 0⟩
  · rintro ⟨c, rfl⟩
    rw [Matrix.smul_mulVec]
    have hconst : Matrix.mulVec (neumannLaplacian n) (fun _ ↦ c) = 0 := by
      rw [show (fun _ ↦ c) = c • fun _ ↦ (1 : ℝ) by
        ext i
        simp]
      rw [Matrix.mulVec_smul]
      simp [neumannLaplacian_mulVecOne_eqZero n]
    simp [hconst]
