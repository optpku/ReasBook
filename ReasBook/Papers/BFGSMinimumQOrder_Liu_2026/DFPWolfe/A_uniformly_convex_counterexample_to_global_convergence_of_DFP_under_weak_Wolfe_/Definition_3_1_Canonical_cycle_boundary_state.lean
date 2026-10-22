/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Definition_3_1_Canonical_cycle_boundary_state.lean
-/

module

public import ReasLib.Optimization.DFP.CycleBoundaryState

public section

open scoped Matrix.Norms.L2Operator

/- Definition 3.1 (Canonical cycle-boundary state): the explicit constructor and its
metric and gradient formulas, with Euclidean vector norms and spectral matrix norms. -/
#check (CycleBoundaryState.ofParams :
  (e : EuclideanSpace ℝ (Fin 2)) → (r p h amplitude : ℝ) → ‖e‖ = 1 →
    0 < r → 0 < p → 0 < h → 0 < amplitude → CycleBoundaryState)

#check (CycleBoundaryState.spec :
  (s : CycleBoundaryState) →
    s.metric = s.frame * Matrix.diagonal ![s.h * s.p * s.r ^ 2, s.h] * s.frame.transpose ∧
      s.gradient = s.amplitude •
        (Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
          (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) s.frame
            !₂[(1 : ℝ), s.p * s.r])

#check (EuclideanSpace.norm_eq :
  (x : EuclideanSpace ℝ (Fin 2)) → ‖x‖ = √(∑ i, ‖x.ofLp i‖ ^ 2))

#check (Matrix.l2_opNorm_def :
  (A : Matrix (Fin 2) (Fin 2) ℝ) →
    ‖A‖ = ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A‖)
