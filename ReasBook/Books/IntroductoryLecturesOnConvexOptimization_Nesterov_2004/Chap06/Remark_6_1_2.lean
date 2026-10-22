/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 6.1.2 lies in the chapter's primal-dual weak-duality / no-gap closure domain.

Primary domain:
- order-theoretic closure of the primal/adjoint bounds `f^* ≤ f_*` and `f_* ≤ f^*`

Sampled owner-style declarations:
- `StructuredObjectiveModel.weakDuality` in `Chap06/Proposition_6_4`, the chapter owner theorem
  supplying the weak-duality bound `f_* ≤ f^*`
- `LagrangianProblem.noDualityGap_of_primalOptimalValue_le_dualOptimalValue` in
  `Chap06/Proposition_6_12`, the chapter-level owner-pattern that packages a reverse bound with
  the relevant weak-duality theorem
- `le_antisymm`, the canonical order owner that turns opposite inequalities into equality
- the linear-order instance on `ℝ`, which specializes `le_antisymm` to scalar primal/adjoint
  values with no extra wrapper data

Best owner abstraction:
- source-facing: the no-duality-gap conclusion from the reverse inequality `(6.1.28)`
- core/canonical: `le_antisymm`
- bridge/view: the specialization of `le_antisymm` to the scalar primal and adjoint optimal
  values, with the weak-duality side supplied upstream by `StructuredObjectiveModel.weakDuality`

Primitive data:
- two scalar values `primalOptimalValue adjointOptimalValue : ℝ`
- the opposite inequalities between them

Derived API:
- the equality `primalOptimalValue = adjointOptimalValue`

Source/core/bridge triage:
- source-facing: no duality gap for the primal-dual pair once `(6.1.28)` gives the reverse bound
- core/canonical: `le_antisymm`
- bridge/view: interpreting the two scalar inequalities as the primal/adjoint value bounds

This item adds no new mathematical owner beyond antisymmetry in a linear order. Keeping a local
theorem named for primal and adjoint values would duplicate the canonical owner with an exact
interface shell, so the file is refined to a pure recall surface. -/

/- Remark 6.1.2 uses the canonical antisymmetry owner directly. -/
recall le_antisymm {α : Type*} [PartialOrder α] {a b : α} : a ≤ b → b ≤ a → a = b

example {primalOptimalValue adjointOptimalValue : ℝ}
    (hgap : primalOptimalValue ≤ adjointOptimalValue)
    (hweak : adjointOptimalValue ≤ primalOptimalValue) :
    primalOptimalValue = adjointOptimalValue :=
  le_antisymm hgap hweak
