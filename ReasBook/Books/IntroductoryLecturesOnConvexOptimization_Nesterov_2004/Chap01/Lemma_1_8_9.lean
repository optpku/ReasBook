/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_8_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Lemma 1.8.9 lies in the variable-metric / quasi-Newton recursion domain.

Primary domain:
* variable-metric and quasi-Newton methods on Euclidean space

Sampled owner-style declarations:
* `VariableMetricMethod.metric`
* `VariableMetricMethod.metric_inv_eq_inverseMetric`
* `VariableMetricMethod.x_succ_eq_sub_metric_inv_gradient`
* `hessianMatrix`

Best owner abstraction:
* `VariableMetricMethod.x_succ_eq_sub_metric_inv_gradient`

Primitive data:
* a variable-metric method `method`
* the unit-step specialization `method.stepSize = 1`

Derived/contextual API:
* the metric sequence `Gₖ = Hₖ⁻¹`
* the local-minimum and Hessian-limit quasi-Newton context often used around this recursion

Source/core/bridge triage:
* source-facing: the unit-step quasi-Newton iterate identity
* core/canonical: `VariableMetricMethod.x_succ_eq_sub_metric_inv_gradient`
* bridge/view: the surrounding local-minimum / Hessian-limit interpretation, which does not alter
  the displayed recursion formula

The former file packaged extra quasi-Newton context into a separate predicate and then restated the
owner theorem through that wrapper. The recursion formula itself only depends on the unit-step
specialization, so this refinement keeps the owner theorem directly as the public entry. -/

recall VariableMetricMethod.x_succ_eq_sub_metric_inv_gradient
    {f : E → ℝ} {x0 : E}
    (method : VariableMetricMethod f x0)
    (hstep : method.stepSize = 1) (k : ℕ) :
    method (k + 1) =
      method k -
        ((method.metric k)⁻¹).toEuclideanLin (∇ f (method k))
