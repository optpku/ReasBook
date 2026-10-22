/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_10_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace LagrangianProblem

/- Proposition 6.12 lies in the Chapter 6 Lagrangian-duality domain.

Primary domain:
- no-duality-gap consequences for the Chapter 1 owner `LagrangianProblem`

Sampled owner-style declarations:
- `LagrangianProblem.primalOptimalValue` and `LagrangianProblem.dualOptimalValue` in
  `Chap01/Definition_1_10_2`
- `LagrangianProblem.dualOptimalValue_le_primalOptimalValue` in `Chap01/Proposition_1_10_8`
- the scalar antisymmetry pattern in `Chap06/Remark_6_1_2`

Best owner abstraction:
- `problem : LagrangianProblem Q m`

Primitive data:
- the owner `problem`

Derived API:
- `problem.primalOptimalValue`
- `problem.dualOptimalValue`
- weak duality `problem.dualOptimalValue_le_primalOptimalValue`

Source/core/bridge triage:
- source-facing: the no-gap conclusion from the reverse inequality `f* ≤ f_*`
- core/canonical: the Chapter 1 owner theorem `problem.dualOptimalValue_le_primalOptimalValue`
- bridge/view: this file packages antisymmetry with the assumed reverse inequality

There is no new mathematical owner here. The statement is a thin bridge from the assumed reverse
bound to equality, so the proof should reuse the Chapter 1 weak-duality owner theorem directly
instead of keeping any parallel local duality API.
-/

/-- Proposition 6.12: if the primal optimal value of a Lagrangian problem is bounded above by its
dual optimal value, then there is no duality gap, so the primal and dual optimal values are
equal. -/
-- Proof sketch: combine the assumed inequality `f* ≤ f_*` with weak duality
-- `f_* ≤ f*` for Lagrangian problems, and conclude by antisymmetry.
theorem noDualityGap_of_primalOptimalValue_le_dualOptimalValue
    {Q : Type u} {m : ℕ} (problem : LagrangianProblem Q m)
    (h : problem.primalOptimalValue ≤ problem.dualOptimalValue) :
    problem.primalOptimalValue = problem.dualOptimalValue := by
  exact le_antisymm h problem.dualOptimalValue_le_primalOptimalValue

end LagrangianProblem
