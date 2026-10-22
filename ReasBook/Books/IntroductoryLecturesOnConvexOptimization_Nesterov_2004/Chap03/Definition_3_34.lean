/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u}

/- Definition 3.34 lies in the chapter's nonsmooth first-order black-box complexity domain.

Sampled owner-style declarations:
* `IsInLipschitzConvexProblemClass` in `Theorem_3_2_1`, the source-facing owner predicate for the
  class `𝒫(x₀, R, M)`;
* `IsMinOn f Set.univ xStar` in mathlib, the canonical owner of the chosen minimizer data for an
  unconstrained objective;
* `SetConstrainedMinimizationProblem.unconstrained f` in `Chap01/Definition_1_3_3`, the canonical
  Chapter 1 whole-space owner for the same objective;
* `SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le` in
  `Chap02/Definition_2_8`, the canonical owner bridge from the whole-space approximate-minimizer
  predicate to the textbook objective-gap inequality.

Best owner abstraction:
* source-facing: the textbook `ε`-approximate-solution notion for an objective in `𝒫(x₀, R, M)`,
  expressed directly as the objective-gap predicate relative to a chosen minimizer `xStar`;
* core/canonical: `SetConstrainedMinimizationProblem.unconstrained f` together with
  `IsMinOn f Set.univ xStar`;
* bridge/view:
  `SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le`.

Primitive data:
* the objective `f : E → ℝ`;
* the chosen minimizer `xStar : E`.

Derived API:
* the source-facing predicate `IsApproximateSolution f xStar ε xBar`;
* the bridge equating `IsApproximateSolution` with the Chapter 1 approximate-minimizer predicate
  for `SetConstrainedMinimizationProblem.unconstrained f`.

This file therefore removes the old bundled-problem wrapper surface. Definition 3.34 is stated
directly on `f` and `xStar`, while the whole-space Chapter 1 owner remains only a thin bridge
proved from `IsMinOn`.
-/

/-- Definition 3.34: relative to a chosen minimizer `x*`, a point `x̄` is an `ε`-approximate
solution of the unconstrained objective `f` when its objective gap above `f(x*)` is at most
`ε`. -/
def IsApproximateSolution (f : E → ℝ) (xStar : E) (ε : ℝ) (xBar : E) : Prop :=
  f xBar - f xStar ≤ ε

variable {f : E → ℝ} {xStar xBar : E}

/-- If `x*` globally minimizes `f`, then the source-facing approximate-solution predicate is
exactly the Chapter 1 approximate-minimizer predicate for the ambient whole-space owner. -/
theorem isApproximateSolution_iff_isApproximateMinimizer
    (hxStar : IsMinOn f Set.univ xStar) (ε : ℝ) (xBar : E) :
    IsApproximateSolution f xStar ε xBar ↔
      (SetConstrainedMinimizationProblem.unconstrained f).IsApproximateMinimizer ε xBar := by
  simpa [IsApproximateSolution] using
    (SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le
      f hxStar ε).symm

theorem isApproximateSolution_iff_isApproximateMinimizer_nnreal
    (hxStar : IsMinOn f Set.univ xStar) (ε : NNReal) (xBar : E) :
    IsApproximateSolution f xStar ε xBar ↔
      (SetConstrainedMinimizationProblem.unconstrained f).IsApproximateMinimizer ε xBar := by
  simpa using isApproximateSolution_iff_isApproximateMinimizer hxStar (ε : ℝ) xBar

end
