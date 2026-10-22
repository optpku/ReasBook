/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_1_Euclidean_gradient_Hessian_and_matrix_operator_bridge_Hessian.lean
-/

module

public import ReasLib.Analysis.Calculus.EuclideanPlaneHessian

/- Compatibility bridge for the Euclidean-plane operator-valued Hessian. -/
#check (EuclideanPlane.hessian :
  (EuclideanSpace ℝ (Fin 2) → ℝ) → EuclideanSpace ℝ (Fin 2) →
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
