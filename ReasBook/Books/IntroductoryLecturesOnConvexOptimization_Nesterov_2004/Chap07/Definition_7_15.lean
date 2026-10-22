/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Remark_6_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Definition 7.15 lies in the chapter's prox-smoothed support-function domain.

Sampled owner-style declarations:
- `supportFunction` in `Chap03/Definition_3_9`, the unsmoothed support-function owner;
- `smoothedPrimalObjective` and `smoothedPrimalObjectiveMaximand` in `Chap06/Definition_6_30`,
  the chapter's canonical regularized-max owner;
- `quadraticDistanceTo` in `Chap06/Remark_6_1_1`, the chapter owner of the Euclidean quadratic
  prox term;
- `continuousLocationSmoothApproximation` and `quadratic_box_smoothed_objective` in
  `Chap06/Definition_6_16` and `Chap06/Definition_6_24`, which show the owner-style for
  source-facing smoothing specializations.

Best owner abstraction:
- source-facing: Definition 7.15's smoothed support-function approximation formula;
- core/canonical: `smoothedPrimalObjective`;
- bridge/view: this numbered file, which only specializes the Chapter 6 owner through the
  matrix-to-dual map `x ↦ innerSL ℝ (A x)` and the prox term `quadraticDistanceTo 0`.

Primitive data:
- the feasible dual set `Q₂`, the matrix `A`, and the positive smoothing parameter `μ`.

Derived API:
- the Euclidean prox term, reused from `quadraticDistanceTo 0`;
- the regularized supremum formula, reused from `smoothedPrimalObjective_apply`.

The previous public alias was a duplicate wheel: the Euclidean prox term is already owned by
`quadraticDistanceTo`, and the regularized-max construction is already owned by
`smoothedPrimalObjective`. This file is therefore recall-first: the numbered item is presented by
direct reuse of the specialized Chapter 6 owner, with only the textbook expansion kept as a
companion theorem. -/

/-- The matrix-to-dual map `x ↦ (u ↦ ⟪Ax, u⟫)` used to specialize the chapter smoothing owner to
Definition 7.15. -/
def supportFunctionSmoothingMap
    (A : Matrix (Fin m) (Fin n) ℝ) : Eₙ →L[ℝ] StrongDual ℝ Eₘ :=
  (innerSL ℝ).comp A.toEuclideanLin.toContinuousLinearMap

@[simp] private theorem supportFunctionSmoothingMap_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Eₙ) (u : Eₘ) :
    supportFunctionSmoothingMap A x u = inner ℝ (A.toEuclideanLin x) u := by
  simp [supportFunctionSmoothingMap, innerSL_apply_apply]

section

variable (Q2 : Set Eₘ) (A : Matrix (Fin m) (Fin n) ℝ) (μ : {μ : ℝ // 0 < μ}) (x : Eₙ)

/- Definition 7.15 is the Chapter 6 regularized-supremum owner specialized to the matrix-to-dual
map `x ↦ (u ↦ ⟪Ax, u⟫)`, zero smooth terms, and the Euclidean prox term
`d₂(u) = (1 / 2) ‖u‖² = quadraticDistanceTo 0 u`. -/
recall smoothedPrimalObjective

set_option linter.hashCommand false in
#check
  smoothedPrimalObjective
    (supportFunctionSmoothingMap A)
    Q2
    0
    0
    (quadraticDistanceTo (0 : Eₘ))
    (μ : ℝ)
    x

end

/- The source-facing companion theorem expands the specialized owner back to the textbook
support-function smoothing formula. -/
@[simp] theorem smoothedPrimalObjective_supportFunction_apply
    (Q2 : Set Eₘ) (A : Matrix (Fin m) (Fin n) ℝ) (μ : ℝ) (x : Eₙ) :
    smoothedPrimalObjective
      (supportFunctionSmoothingMap A)
      Q2
      0
      0
      (quadraticDistanceTo (0 : Eₘ))
      μ
      x =
      sSup ((fun u : Eₘ ↦
        inner ℝ (A.toEuclideanLin x) u - μ * ((1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ))) '' Q2) := by
  rw [smoothedPrimalObjective_apply]
  simp only [Pi.zero_apply, zero_add]
  apply congrArg sSup
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    simp [smoothedPrimalObjectiveMaximand]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    simp [smoothedPrimalObjectiveMaximand]

end
