/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 2.45 is a recall-only item in the chapter's functional-constraint max-type
value-function domain.

Sampled owner-style declarations:
* `LagrangianProblem.constrainedAuxiliaryObjective` in `Lemma_2_21`, the canonical auxiliary
  max-type objective `x ↦ max {f₀(x) - t, f₁(x), …, fₘ(x)}`;
* `LagrangianProblem.constrainedAuxiliaryOptimalValue` in `Lemma_2_21`, the generic owner infimum
  of the same max-violation objective on an ambient type;
* `LagrangianProblem.constrainedAuxiliaryOptimalValue_eq_of_isMinOn` in `Lemma_2_21`, the owner
  attained-minimum theorem reused on restricted subtype problems when needed;
* `maxTypeObjective_apply` in `Definition_2_39`, the canonical finite-maximum evaluation theorem
  used to expose the textbook pointwise formula from the owner max-type objective.

Best owner abstraction:
* core/canonical:
  `LagrangianProblem.mk (fun x : Q ↦ f0 x) (fun i x ↦ fi i x) : LagrangianProblem Q m`;
* source-facing:
  the owner objective
  `LagrangianProblem.constrainedAuxiliaryObjective
    (LagrangianProblem.mk (fun x : Q ↦ f0 x) (fun i x ↦ fi i x)) t`
  and the corresponding owner value on `Q`;
* bridge/view:
  `LagrangianProblem.constrainedAuxiliaryOptimalValue_eq_sInf`, which expands the owner value to
  the textbook constrained infimum formula.

Primitive data:
* feasible set `Q`;
* objective `f0`;
* constraint family `fi`;
* scalar parameter `t`.

Derived API:
* the subtype owner
  `LagrangianProblem.mk (fun x : Q ↦ f0 x) (fun i x ↦ fi i x) : LagrangianProblem Q m`;
* the parametric max-type objective on `Q`;
* its constrained owner value on `Q`;
* the restricted-attainment bridge furnished by the generic `LagrangianProblem` theorem.

This recall file intentionally introduces no parallel public wrappers such as
`functionalConstraintValueObjective`, `functionalConstraintValueFunction`, or a specialized
`..._eq_of_isMinOn` theorem. Downstream files should use the owner max-type expression and the
corresponding subtype owner value directly. -/

recall LagrangianProblem.constrainedAuxiliaryObjective
recall LagrangianProblem.constrainedAuxiliaryOptimalValue
recall LagrangianProblem.constrainedAuxiliaryOptimalValue_eq_sInf
recall LagrangianProblem.constrainedAuxiliaryOptimalValue_eq_of_isMinOn
