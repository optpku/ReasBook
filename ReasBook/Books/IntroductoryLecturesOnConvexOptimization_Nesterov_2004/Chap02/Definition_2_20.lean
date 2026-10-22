/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Primary domain: smooth unconstrained minimization on `ℝⁿ`.

Sampled owner-style declarations:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`, the positive-`μ` owner predicate;
* `ConvexC1SeminormSmooth (normSeminorm ℝ E) L f` in `Theorem_2_5`, the `μ = 0`
  smooth-convex owner predicate;
* `IsMinOn f Set.univ xStar` together with `isMinOn_univ_iff`, the canonical whole-space
  minimizer owner and its textbook inequality view;
* `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  owner for the attained optimal value `f^*`.

Best owner abstraction:
* source-facing: the objective `f : E → ℝ`, together with either `f ∈ 𝓢[μ, L]¹¹` when `0 < μ`
  or `f ∈ 𝓕[L, p]¹¹` when `μ = 0`, and the whole-space minimizer predicate
  `IsMinOn f Set.univ xStar`;
* core/canonical: `SetConstrainedMinimizationProblem.unconstrained f` for the associated
  unconstrained problem, plus `IsMinOn f Set.univ xStar` for an optimal solution;
* bridge/view: the owner-namespace unconstrained specialization
  `SetConstrainedMinimizationProblem.unconstrained_optimalValue_eq_of_isMinOn`.

Primitive data:
* the objective `f : E → ℝ`;
* optionally, an optimizer `xStar : E` with `IsMinOn f Set.univ xStar`.

Derived API:
* the whole-space problem owner `SetConstrainedMinimizationProblem.unconstrained f`;
* the textbook inequality form `∀ x, f xStar ≤ f x` from `isMinOn_univ_iff`;
* the attained optimal value identity from the owner-namespace theorem
  `SetConstrainedMinimizationProblem.unconstrained_optimalValue_eq_of_isMinOn`.

Definition 2.20 therefore reuses the canonical whole-space minimization owner from Chapter 1 and
the canonical whole-space minimizer predicate from mathlib, instead of introducing a parallel
`SmoothMinimizationProblem` wrapper or an alias for “optimal solution”. -/

section ProblemOwner

variable (f : E → ℝ)

/-- Definition 2.20: for a smooth convex objective `f ∈ 𝓕[L, p]¹¹` or a strongly convex smooth
objective `f ∈ 𝓢[μ, L]¹¹`, the associated unconstrained minimization problem
`min_{x ∈ ℝⁿ} f(x)` is the canonical whole-space owner
`SetConstrainedMinimizationProblem.unconstrained f`. If `xStar` satisfies
`IsMinOn f Set.univ xStar`, then `xStar` is an optimal solution and the optimal value is given by
the companion theorem
`SetConstrainedMinimizationProblem.unconstrained_optimalValue_eq_of_isMinOn`. -/
theorem associated_unconstrained_problem_eq_unconstrained :
    ({ feasibleSet := Set.univ, objective := f } : SetConstrainedMinimizationProblem E) =
      SetConstrainedMinimizationProblem.unconstrained f :=
  rfl

end ProblemOwner

namespace SetConstrainedMinimizationProblem

variable {X : Type u} (f : X → ℝ) {xStar : X}

/-- Helper for Definition 2.20: every ambient point is feasible for the unconstrained
minimization problem associated with `f`. -/
theorem mem_unconstrained_feasibleSet (x : X) :
    x ∈ (unconstrained f).feasibleSet := by
  -- The unconstrained feasible region is the whole ambient space.
  simp [unconstrained_feasibleSet]

/-- The unconstrained owner optimal value is the attained value `f xStar` whenever `xStar`
minimizes `f` on all of the ambient space. -/
-- Proof sketch: package `f` as the Chapter 1 whole-space problem on `Set.univ`, apply
-- `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn`, and simplify the trivial
-- feasibility witness `xStar ∈ Set.univ`.
theorem unconstrained_optimalValue_eq_of_isMinOn
    (hmin : IsMinOn f Set.univ xStar) :
    (unconstrained f).optimalValue = (f xStar : EReal) := by
  -- Any ambient point is feasible for the whole-space owner.
  have hxStar : xStar ∈ (unconstrained f).feasibleSet :=
    mem_unconstrained_feasibleSet (f := f) xStar
  -- Apply the Chapter 1 attained-optimal-value theorem to the whole-space owner.
  simpa using
    (unconstrained f).optimalValue_eq_of_isMinOn hxStar hmin

end SetConstrainedMinimizationProblem
