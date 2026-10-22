/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.1 is a bridge/view item for the Chapter 1 owner theorem on second-order local
minimality.

Relevant owner declarations sampled before refinement:
* `isLocalMin_gradient_eq_zero_and_hessian_isPositive` from `Theorem_1_4_20`
* `∇²` / `hessianMatrix` from `Definition_1_4_16`
* `Matrix.isPositive_toEuclideanLin_iff`

Best owner abstraction:
* `ContinuousLinearMap.IsPositive (hessian f xStar)`

Primitive data:
* the Chapter 1 owner theorem above
* the Euclidean Hessian matrix owner `∇²`

Derived API:
* the matrix positive-semidefiniteness conclusion

Source/core/bridge triage:
* source-facing: the Euclidean second-order necessary condition stated with the Hessian matrix
* core/canonical: `isLocalMin_gradient_eq_zero_and_hessian_isPositive`
* bridge/view: `Matrix.isPositive_toEuclideanLin_iff`

This file therefore keeps only the bridge to the matrix view instead of repeating the
local-minimizer argument with a parallel Hessian definition. -/

/-- Proposition 4.1.1: if `f` is `C²` at a local minimizer `xStar : ℝⁿ`, then the gradient
vanishes and the Hessian is positive semidefinite at `xStar`. -/
-- Proof sketch: apply the owner theorem `isLocalMin_gradient_eq_zero_and_hessian_isPositive`,
-- then convert positivity of the Euclidean Hessian matrix operator
-- `((∇² f xStar).toEuclideanLin)` to positive semidefiniteness using
-- `Matrix.isPositive_toEuclideanLin_iff`.
theorem local_minimizer_gradient_eq_zero_and_hessian_posSemidef
    (f : E → ℝ) (xStar : E) (hf : ContDiffAt ℝ 2 f xStar) (hmin : IsLocalMin f xStar) :
    ∇ f xStar = 0 ∧ (∇² f xStar).PosSemidef := by
  rcases isLocalMin_gradient_eq_zero_and_hessian_isPositive hf hmin with ⟨hgrad, hH⟩
  refine ⟨hgrad, ?_⟩
  exact Matrix.isPositive_toEuclideanLin_iff.mp <| by
    simpa [hessianMatrix_toEuclideanLin] using hH.toLinearMap
