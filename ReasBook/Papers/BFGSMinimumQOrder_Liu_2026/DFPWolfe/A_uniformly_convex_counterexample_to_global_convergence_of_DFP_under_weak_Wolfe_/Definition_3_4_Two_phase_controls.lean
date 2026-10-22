/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Definition_3_4_Two_phase_controls.lean
-/

module

public import ReasLib.Optimization.DFP.CycleBoundaryState
public import ReasLib.Optimization.DFP.TwoPhaseControls
public import ReasLib.LinearAlgebra.Matrix.OrientedEigenframe

public section

noncomputable section

open scoped Matrix

/- Definition 3.4 (Two-phase controls): use `radius ε = ε ^ 2` and the ordered
family `phase ε` on both legs.  After each updated matrix and gradient, use
`OrientedEigenframe.frame` before recovering canonical coordinates with
`CycleBoundaryState.ofParams`. -/
#check (TwoPhaseControls.phase : ℝ → Fin 2 → PlanarDFPControl)
#check (TwoPhaseControls.radius_def : ∀ ε : ℝ, TwoPhaseControls.radius ε = ε ^ 2)
#check (TwoPhaseControls.first_matrix : ∀ ε : ℝ,
  (TwoPhaseControls.first ε).matrix = !![1, ε; ε, 1])
#check (TwoPhaseControls.first_tau : ∀ ε : ℝ,
  (TwoPhaseControls.first ε).tau = 2 / 3)
#check (TwoPhaseControls.second_matrix : ∀ ε : ℝ,
  (TwoPhaseControls.second ε).matrix = !![1, -2 * ε; -2 * ε, 1])
#check (TwoPhaseControls.second_tau : ∀ ε : ℝ,
  (TwoPhaseControls.second ε).tau = 1 / 3)
#check (TwoPhaseControls.matrix_posDef : ∀ (ε ε₀ : ℝ) (i : Fin 2),
  0 < ε → ε ≤ ε₀ → ε₀ < 1 / 4 → Matrix.PosDef (TwoPhaseControls.phase ε i).matrix)
#check (TwoPhaseControls.spectrum_mem : ∀ (ε ε₀ : ℝ) (i j : Fin 2),
  0 < ε → ε ≤ ε₀ → ε₀ < 1 / 4 →
    (TwoPhaseControls.matrix_isHermitian ε i).eigenvalues j ∈ Set.Icc (1 / 2) (3 / 2))
#check (OrientedEigenframe.lowVector :
  ℝ → ℝ → ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
#check (OrientedEigenframe.lowVector_hasEigenvector : ∀ (a b d : ℝ)
  (g : EuclideanSpace ℝ (Fin 2)), a < d →
    Module.End.HasEigenvector
      ((Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
        (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)))
          (RealSymmetric2.matrix a b d)).toLinearMap
      (RealSymmetric2.low a b d) (OrientedEigenframe.lowVector a b d g))
#check (OrientedEigenframe.inner_lowVector_pos : ∀ (a b d : ℝ)
  (g : EuclideanSpace ℝ (Fin 2)),
    inner ℝ (RealSymmetric2.lowVector a b d) g ≠ 0 →
      0 < inner ℝ (OrientedEigenframe.lowVector a b d g) g)
#check (OrientedEigenframe.frame_mem_specialOrthogonalGroup : ∀ (a b d : ℝ)
  (g : EuclideanSpace ℝ (Fin 2)), a < d →
    OrientedEigenframe.frame a b d g ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
#check (OrientedEigenframe.frame_diagonalizes : ∀ (a b d : ℝ)
  (g : EuclideanSpace ℝ (Fin 2)), a < d →
    (OrientedEigenframe.frame a b d g).transpose * RealSymmetric2.matrix a b d *
        OrientedEigenframe.frame a b d g =
      Matrix.diagonal ![RealSymmetric2.low a b d, RealSymmetric2.high a b d])
#check (CycleBoundaryState.ofParams : ∀ (e : EuclideanSpace ℝ (Fin 2))
  (r p h amplitude : ℝ), ‖e‖ = 1 → 0 < r → 0 < p → 0 < h → 0 < amplitude →
    CycleBoundaryState)
