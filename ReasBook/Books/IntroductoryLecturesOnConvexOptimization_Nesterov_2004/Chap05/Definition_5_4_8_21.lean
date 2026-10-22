/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_8_9

-- Declarations for this item will be appended below by the statement pipeline.

/-
Definition 5.4.8.21 lies in the Chapter 5 box-constrained `ℓ_p` approximation epigraph domain.

Sampled owner declarations:
- `LpApproximationEpigraphPoint` in `Theorem_5_4_8_9`, the chapter owner for the lifted
  epigraph decision variable `(x, τ⁽⁰⁾, τ⁽¹⁾, ..., τ⁽ᵐ⁾)`;
- `LpApproximationEpigraphPoint.objectiveSlack` in `Theorem_5_4_8_9`, the canonical projection to
  the scalar slack `τ⁽⁰⁾`;
- `lpApproximationEpigraphProblem` in `Theorem_5_4_8_9`, the chapter owner for the epigraph
  reformulation;
- `mem_lpApproximationEpigraphProblem_feasibleSet_iff` in `Theorem_5_4_8_9`, the atomic
  membership view of that owner feasible set.

Best owner abstraction:
- source-facing: the textbook epigraph reformulation of the box-constrained `ℓ_p`
  approximation problem;
- core/canonical: `LpApproximationEpigraphPoint` and `lpApproximationEpigraphProblem`;
- bridge/view: the evaluation and membership lemmas expanding those owners to the displayed
  inequalities.

Primitive data:
- the lifted decision-variable type `LpApproximationEpigraphPoint n m`.

Derived API:
- the objective projection `LpApproximationEpigraphPoint.objectiveSlack`;
- the epigraph owner `lpApproximationEpigraphProblem p a b α β`;
- the companion lemmas `lpApproximationEpigraphProblem_apply` and
  `mem_lpApproximationEpigraphProblem_feasibleSet_iff`.

Source/core/bridge triage:
- source-facing: Definition 5.4.8.21's epigraph standard-form variables and inequalities;
- core/canonical: the existing chapter owner declarations from `Theorem_5_4_8_9`;
- bridge/view: the companion expansion lemmas for objective evaluation and feasible-set
  membership.

This item therefore deletes the duplicate local structure
`LpApproximationEpigraphDecisionVariable`, the duplicate feasible-set definition
`lpApproximationEpigraphStandardForm`, and the duplicate objective alias. The existing chapter
owner API should be used directly.
-/

recall LpApproximationEpigraphPoint
recall LpApproximationEpigraphPoint.objectiveSlack
recall lpApproximationEpigraphProblem
recall mem_lpApproximationEpigraphProblem_feasibleSet_iff
recall lpApproximationEpigraphProblem_apply

/- Definition 5.4.8.21 recalls the chapter owner for the `ℓ_p` approximation epigraph decision
variables. -/
#check LpApproximationEpigraphPoint

/- Definition 5.4.8.21 recalls the coordinate projection to the epigraph objective slack. -/
#check LpApproximationEpigraphPoint.objectiveSlack

/- Definition 5.4.8.21 recalls the chapter owner for the corresponding epigraph reformulation. -/
#check lpApproximationEpigraphProblem
