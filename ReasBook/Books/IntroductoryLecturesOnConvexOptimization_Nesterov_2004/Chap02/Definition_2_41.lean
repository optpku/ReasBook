/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_40

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

noncomputable section

universe u

/- Definition 2.41 is source-facing in the constrained parametric minimization domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
* `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical
  constrained minimizer set;
* `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  optimal-value owner;
* `maxTypeGradientMapping` and `maxTypeReducedGradient` in `Remark_2_41_1`, the later chosen-step
  specialization of the present general definitions.

Best owner abstraction:
* the constrained problem with feasible set `Q` and objective `x ↦ fγ xBar x`;
* its canonical minimizer set `argmin[Q] (fγ xBar)`.

Primitive data:
* a feasible set `Q : Set E`;
* a parameterized model `fγ : E → E → ℝ`;
* a base point `xBar : E`.

Derived API:
* the canonical constrained optimal set `gradientMappingSet Q fγ xBar`;
* the canonical optimal value `gradientMappingOptimalValue Q fγ xBar`;
* for a chosen minimizing point `x`, the reduced gradient `reducedGradientOf γ xBar x`.

Source/core/bridge triage:
* source-facing: the gradient-mapping set and reduced gradient from Definition 2.41;
* core/canonical: `SetConstrainedMinimizationProblem`, `argmin[Q]`, and `optimalValue`;
* bridge/view: the realization theorem identifying the canonical optimal value at any
  `x ∈ gradientMappingSet Q fγ xBar`.

This file therefore keeps the source-facing minimizer set and reduced-gradient formula, while
reusing the Chapter 1 owner API for constrained argmin sets and optimal values. -/

section

variable {E : Type u}

/-- Definition 2.41: the textbook set `X_f(xBar; γ)` of gradient mappings is the constrained
argmin set of the model `x ↦ fγ xBar x` on `Q`. The corresponding canonical optimal value is
`gradientMappingOptimalValue Q fγ xBar`, and any chosen `x ∈ gradientMappingSet Q fγ xBar`
determines the reduced gradient `reducedGradientOf γ xBar x`. -/
abbrev gradientMappingSet
    (Q : Set E) (fγ : E → E → ℝ) (xBar : E) :
    Set E :=
  argmin[Q] (fγ xBar)

/-- The canonical optimal value of the gradient-mapping subproblem, viewed in `EReal`. -/
abbrev gradientMappingOptimalValue
    (Q : Set E) (fγ : E → E → ℝ) (xBar : E) :
    EReal :=
  ((.mk Q (fγ xBar)) : SetConstrainedMinimizationProblem E).optimalValue

/-- Membership in the gradient-mapping set means feasibility and minimality for the model
`x ↦ fγ xBar x` on `Q`. -/
-- Proof sketch: this is exactly `mem_constrainedArgmin_iff` for the objective `fγ xBar`.
theorem mem_gradientMappingSet_iff
    {Q : Set E} {fγ : E → E → ℝ} {xBar x : E} :
    x ∈ gradientMappingSet Q fγ xBar ↔ x ∈ Q ∧ IsMinOn (fγ xBar) Q x := by
  change x ∈ argmin[Q] (fγ xBar) ↔ x ∈ Q ∧ IsMinOn (fγ xBar) Q x
  exact mem_constrainedArgmin_iff

/-- Any gradient mapping realizes the canonical optimal value of the subproblem at `xBar`. -/
-- Proof sketch: extract feasibility and minimality from `mem_gradientMappingSet_iff`, then apply
-- `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn` to the canonical owner whose
-- feasible set is `Q` and whose objective is `fγ xBar`.
theorem gradientMappingOptimalValue_eq_of_mem_gradientMappingSet
    {Q : Set E} {fγ : E → E → ℝ} {xBar x : E}
    (hx : x ∈ gradientMappingSet Q fγ xBar) :
    gradientMappingOptimalValue Q fγ xBar = (fγ xBar x : EReal) := by
  rw [mem_gradientMappingSet_iff] at hx
  let problem : SetConstrainedMinimizationProblem E :=
    .mk Q (fγ xBar)
  change problem.optimalValue = (problem x : EReal)
  exact problem.optimalValue_eq_of_isMinOn hx.1 hx.2

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- The reduced gradient attached to a chosen gradient mapping `x` is the scaled residual
`γ (xBar - x)`. -/
def reducedGradientOf
    (γ : ℝ) (xBar x : E) :
    E :=
  γ • (xBar - x)

end
