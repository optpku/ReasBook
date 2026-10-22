/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 4.1.3 is a trust-region-constrained second-order local model construction.

Source/core/bridge triage:
* source-facing/core: a chosen trust-region Newton next iterate represented by the canonical
  subtype `{x : E // x ∈ argmin[Metric.closedBall xk ε] (secondOrderTaylorModelAt f xk)}`
* bridge/view: `mem_constrainedArgmin_iff`, which separates closed-ball membership from the
  minimizer predicate attached to that subtype membership

Primitive data:
* `f`
* the current point `xk`
* the trust-region radius `ε`

Derived API:
* the canonical closed-ball argmin set of the quadratic Taylor model
* the chosen next iterate as a point of that argmin set
* the decomposition of its membership into trust-region feasibility and `IsMinOn`

This item adds no new owner beyond the chapter argmin owner and the ambient subtype constructor.
The previous local theorems only duplicated `Subtype.2` and `mem_constrainedArgmin_iff`, so the
file should stay at direct canonical recall/check surface instead of exporting a parallel wrapper
API. Positivity of `ε` and smoothness of `f` remain external side assumptions, not primitive
fields of any local step structure. -/

section

variable (f : E → ℝ) (xk : E) (ε : ℝ)

/- Algorithm 4.1.3 recalls the canonical closed-ball argmin subtype for the quadratic Taylor
model. A chosen trust-region Newton next iterate is represented directly as a point of that
owner object, with no extra wrapper declaration. -/
set_option linter.hashCommand false in
#check ({x : E // x ∈ argmin[Metric.closedBall xk ε] (secondOrderTaylorModelAt f xk)} : Type u)

end

section

variable {f : E → ℝ} {xk : E} {ε : ℝ}

namespace TrustRegionNewton

/-- Algorithm 4.1.3: a chosen trust-region Newton step is feasible for the closed ball and
minimizes the quadratic Taylor model on that trust region. -/
theorem step_spec
    (step :
      {x : E // x ∈ argmin[Metric.closedBall xk ε] (secondOrderTaylorModelAt f xk)}) :
    (step : E) ∈ Metric.closedBall xk ε ∧
      IsMinOn (secondOrderTaylorModelAt f xk) (Metric.closedBall xk ε) (step : E) := by
  -- Unpack constrained argmin membership into feasibility and the `IsMinOn` certificate.
  exact mem_constrainedArgmin_iff.mp step.2

/-- Helper for Algorithm 4.1.3: every chosen trust-region Newton step lies in the trust region. -/
theorem step_mem_closedBall
    (step : {x : E // x ∈ argmin[Metric.closedBall xk ε] (secondOrderTaylorModelAt f xk)}) :
    (step : E) ∈ Metric.closedBall xk ε := by
  -- Project the feasibility half of the canonical argmin decomposition.
  exact (step_spec step).1

/-- Helper for Algorithm 4.1.3: every chosen trust-region Newton step minimizes the quadratic
Taylor model on the trust region. -/
theorem step_isMinOn
    (step : {x : E // x ∈ argmin[Metric.closedBall xk ε] (secondOrderTaylorModelAt f xk)}) :
    IsMinOn (secondOrderTaylorModelAt f xk) (Metric.closedBall xk ε) (step : E) := by
  -- Project the minimizing half of the canonical argmin decomposition.
  exact (step_spec step).2

end TrustRegionNewton

end
