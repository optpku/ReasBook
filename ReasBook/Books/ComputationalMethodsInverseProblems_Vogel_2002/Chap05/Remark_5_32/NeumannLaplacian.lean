/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

import Mathlib.LinearAlgebra.Matrix.Action

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Exercise_5_31.GridGraph

public section

namespace Matrix

/-- The Chapter 5 negative discrete Laplacian with homogeneous Neumann boundary conditions on
the `n_y × n_x` grid, realized as the shared path-product grid graph Laplacian. -/
noncomputable def neumannLaplacian (n_x n_y : ℕ) :
    Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ :=
  (gridGraph n_x n_y).lapMatrix ℝ

/-- The Chapter 5 Neumann discrete Laplacian agrees with the shared path-product grid graph
Laplacian. -/
theorem neumannLaplacian_eqGridLapMatrix (n_x n_y : ℕ) :
    Matrix.neumannLaplacian n_x n_y =
      (gridGraph n_x n_y).lapMatrix ℝ := by
  simp [neumannLaplacian]

/-- The constant-one vector belongs to the kernel of the Chapter 5 Neumann discrete Laplacian. -/
theorem neumannLaplacian_mulVecOne_eqZero (n_x n_y : ℕ) :
    Matrix.mulVec (Matrix.neumannLaplacian n_x n_y) (fun _ ↦ (1 : ℝ)) = 0 := by
  simpa [neumannLaplacian] using
    (gridGraph n_x n_y).lapMatrix_mulVec_const_eq_zero

/-- The Chapter 5 Neumann discrete Laplacian is positive semidefinite. -/
theorem neumannLaplacian_posSemidef (n_x n_y : ℕ) :
    Matrix.PosSemidef (Matrix.neumannLaplacian n_x n_y) := by
  simpa [neumannLaplacian] using
    (gridGraph n_x n_y).posSemidef_lapMatrix ℝ

/-- The kernel of the Chapter 5 Neumann discrete Laplacian consists exactly of the constant
grid functions, provided both grid directions are nonempty. -/
theorem neumannLaplacian_mulVecEqZero_iffExistsConst {n_x n_y : ℕ}
    (h_x : 0 < n_x) (h_y : 0 < n_y) (x : Fin n_y × Fin n_x → ℝ) :
    Matrix.mulVec (Matrix.neumannLaplacian n_x n_y) x = 0 ↔ ∃ c : ℝ, x = fun _ ↦ c := by
  constructor
  · intro hx
    have hgrid :
        Matrix.mulVec ((gridGraph n_x n_y).lapMatrix ℝ) x = 0 := by
      simpa [neumannLaplacian] using hx
    have hreachable :
        ∀ p q : Fin n_y × Fin n_x, x p = x q := by
      have hreachable' :
          ∀ p q : Fin n_y × Fin n_x, (gridGraph n_x n_y).Reachable p q → x p = x q :=
        ((gridGraph n_x n_y).lapMatrix_mulVec_eq_zero_iff_forall_reachable (x := x)).mp hgrid
      exact fun p q ↦ hreachable' p q ((gridGraph_connected h_x h_y).preconnected p q)
    let origin : Fin n_y × Fin n_x := (⟨0, h_y⟩, ⟨0, h_x⟩)
    refine ⟨x origin, funext fun p ↦ ?_⟩
    exact hreachable p origin
  · rintro ⟨c, rfl⟩
    rw [show (fun _ ↦ c) = c • fun _ ↦ (1 : ℝ) by
      ext p
      simp]
    rw [Matrix.mulVec_smul]
    simp [neumannLaplacian_mulVecOne_eqZero]

end Matrix
