/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 5.0.6 is a recall-only item in the Euclidean linear-change-of-variables domain.

Layer targeted by this refinement:
- source-facing recall of the core/canonical pullback `f ∘ B.toEuclideanLin`

Primary domain:
- linear changes of variables on `ℝⁿ`, viewed as precomposition by the linear map
  attached to a matrix.

Sampled owner-style declarations:
- mathlib `Matrix.toEuclideanLin`
- mathlib `Matrix.toEuclideanLin_apply`
- mathlib `Matrix.toEuclideanCLM`
- mathlib `Matrix.coe_toEuclideanCLM_eq_toEuclideanLin`

Best owner abstraction:
- core/canonical: `f ∘ B.toEuclideanLin`

Primitive data:
- `f : E → ℝ`
- `B : Matrix (Fin n) (Fin n) ℝ`

Derived API:
- pointwise evaluation by `Function.comp_apply`
- the matrix-action bridge `Matrix.toEuclideanLin_apply`
- the bundled continuous-linear-map view by `Matrix.coe_toEuclideanCLM_eq_toEuclideanLin`

Source/core/bridge triage:
- source-facing: the textbook pullback under the substitution `x = By`
- core/canonical: precomposition with `B.toEuclideanLin`
- bridge/view: the bundled continuous-linear-map realization `B.toEuclideanCLM`

The previous local abbrev `linearChangeOfVariables` and theorem
`linearChangeOfVariables_apply` were exact-interface duplicates of this canonical composition. The
nonsingularity hypothesis is not primitive data for defining the pullback itself, so the refined
file removes that redundant wrapper and recalls the chapter's established owner surface directly. -/

section

recall Matrix.toEuclideanLin

variable (f : E → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)

/- Definition 5.0.6: the pullback induced by `x = By` is exactly the canonical composition of `f`
with the chapter's owner linear map attached to `B`. -/
#check (f ∘ B.toEuclideanLin : E → ℝ)

end

/- The matrix-action bridge for the canonical pullback is the standard evaluation formula for
`Matrix.toEuclideanLin`. -/
recall Matrix.toEuclideanLin_apply

end
