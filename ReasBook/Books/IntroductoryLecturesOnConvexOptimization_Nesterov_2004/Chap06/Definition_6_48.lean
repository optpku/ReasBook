/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_47

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open RealSymmetricMatrixSpace
open scoped BigOperators RealSymmetricMatrixSpace

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

/- Definition 6.48 lies in Chapter 6's smoothed semidefinite / spectral optimization domain.

Mandatory domain-style sampling before refinement:
- `logSumExpMaxEigenvalueSmoothing` in `Definition_6_47`, the Chapter 6 owner of the
  positive-parameter spectral smoothing on `𝕊^n`;
- `logSumExpMaxEigenvalueSmoothing_eq` in `Definition_6_47`, the direct bridge to the textbook
  eigenvalue log-sum-exp formula;
- `SetConstrainedMinimizationProblem.optimalValue` in `Definition_1_3_7`, the project owner for
  the constrained optimal value of a feasible real-valued objective;
- `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image` in `Definition_1_3_7`, the
  bridge expanding that owner to the `EReal` image infimum;
- `NonsmoothEigenvalueMinimizationProblem.toSetConstrainedMinimizationProblem` and
  `NonsmoothEigenvalueMinimizationProblem.optimalValue_eq` in `Definition_6_46`, the nearby
  Chapter 6 owner pattern for the same semidefinite optimization layer.

Best owner abstraction:
- source-facing: `smoothedSemidefiniteObjective`, the specialization `y ↦ f_μ(C + A y)`;
- core/canonical: `logSumExpMaxEigenvalueSmoothing` and
  `SetConstrainedMinimizationProblem.mk Q (smoothedSemidefiniteObjective n μ C A)`;
- bridge/view: `smoothedSemidefiniteObjective_apply` and the inherited optimal-value owner
  specialization at the end of the file.

Primitive data:
- the ambient real module `E`, with the textbook `ℝ^m` kept only as a specialization layer;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`;
- the symmetric matrix `C : 𝕊^n`;
- the continuous linear map `A : E →L[ℝ] 𝕊^n`;
- the feasible set `Q : Set E` only for the optimal-value surface.

Derived API:
- the source-facing objective specialization `smoothedSemidefiniteObjective`;
- its textbook pointwise expansion;
- the canonical optimal-value surface
  `(SetConstrainedMinimizationProblem.mk Q (smoothedSemidefiniteObjective n μ C A)).optimalValue`.

Source/core/bridge triage:
- source-facing: `smoothedSemidefiniteObjective`;
- core/canonical: `logSumExpMaxEigenvalueSmoothing`,
  `SetConstrainedMinimizationProblem.mk Q (smoothedSemidefiniteObjective n μ C A)`;
- bridge/view: the pointwise expansion theorem and the specialized owner checks below.

The previous version introduced a second public optimal-value definition that was only the Chapter
1 constrained-problem optimal-value owner under a new local name, and also fixed the ambient
decision space to the textbook coordinate model `ℝ^m`. This refinement keeps the source-facing
objective specialization, deletes that duplicate optimal-value wheel, and exposes the affine
composition through an arbitrary real module `E`, with `ℝ^m` available as the intended concrete
specialization.
-/

/-- Definition 6.48: for a symmetric matrix `C ∈ 𝕊^n`, a continuous linear map
`A : E →L[ℝ] 𝕊^n`, and
`μ > 0`, the smoothed semidefinite objective is the Definition 6.47 smoothing evaluated at
`C + A(y)`. The textbook case `E = ℝ^m` is the intended specialization. -/
abbrev smoothedSemidefiniteObjective
    (n : ℕ) (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) : E → ℝ :=
  fun y ↦ logSumExpMaxEigenvalueSmoothing μ (C + A y)

/-- Evaluating the smoothed semidefinite objective recovers the textbook formula
`f_μ(C + A(y))`. -/
theorem smoothedSemidefiniteObjective_apply
    (n : ℕ) (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) (y : E) :
    smoothedSemidefiniteObjective n μ C A y =
      (μ : ℝ) *
        Real.log (∑ i : Fin n, Real.exp (eigenvalues (C + A y) i / (μ : ℝ))) := by
  simpa [smoothedSemidefiniteObjective] using
    logSumExpMaxEigenvalueSmoothing_eq μ (C + A y)

variable (μ : {μ : ℝ // 0 < μ}) (Q : Set E) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n)

/- Definition 6.48 uses the Chapter 1 constrained optimal-value owner directly for the notation
`φ_μ^*`. -/
recall SetConstrainedMinimizationProblem.optimalValue
recall SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image

set_option linter.hashCommand false in
#check
  (SetConstrainedMinimizationProblem.mk Q (smoothedSemidefiniteObjective n μ C A)).optimalValue

set_option linter.hashCommand false in
#check
  (show
      (SetConstrainedMinimizationProblem.mk Q
        (smoothedSemidefiniteObjective n μ C A)).optimalValue =
      sInf ((fun y : E ↦ (smoothedSemidefiniteObjective n μ C A y : EReal)) '' Q) from
    (SetConstrainedMinimizationProblem.mk Q
      (smoothedSemidefiniteObjective n μ C A)).optimalValue_eq_sInf_image)

end

end
