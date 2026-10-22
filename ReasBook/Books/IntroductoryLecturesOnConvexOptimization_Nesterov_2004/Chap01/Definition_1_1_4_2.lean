/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_4_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace GeneralMinimizationProblem

variable {n m : ℕ}

/- Definition 1.1.4.2 is a source-facing recall in the Chapter 1 constrained-optimization owner
domain.

Sampled owner-style declarations:
* `GeneralMinimizationProblem.IsConstrained` in `Definition_1_1_4_1`, the earlier Chapter 1 owner
  predicate for constrainedness;
* `GeneralMinimizationProblem.not_isConstrained_iff_feasibleSet_eq_univ` in
  `Definition_1_1_4_1`, the imported companion bridge from that owner to the textbook whole-space
  formulation;
* the owner expression
  `¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
    problem.toGeneralMinimizationProblem.IsSmooth` together with
  `SetConstrainedMinimizationProblem.unconstrainedSmooth_iff` in `Definition_1_4_3`, the direct
  downstream Chapter 1 reuse of this unconstrainedness predicate;
* `Set.ssubset_univ_iff`, the canonical set-theoretic bridge used upstream to establish that
  companion theorem.

Best owner abstraction:
* source-facing/core: `¬ problem.IsConstrained`
* bridge/view: `GeneralMinimizationProblem.not_isConstrained_iff_feasibleSet_eq_univ`

Primitive data:
* `problem.feasibleSet`
* `problem.IsConstrained`

Derived API:
* none in this recall-only file beyond the imported bridge theorem above

Source/core/bridge triage:
* source-facing: the unconstrainedness predicate `¬ problem.IsConstrained`
* core/canonical: the earlier owner predicate `problem.IsConstrained`
* bridge/view: the whole-space reformulation of the feasible set

This file therefore keeps Definition 1.1.4.2 as a direct recall of the earlier owner predicate,
with the feasible-set equality retained only as the imported thin companion theorem from
`Definition_1_1_4_1` for downstream bridge files. -/

variable (problem : GeneralMinimizationProblem n m)

/- Definition 1.1.4.2: a general minimization problem is unconstrained exactly when the owner
predicate `IsConstrained` does not hold. -/
#check (¬ problem.IsConstrained)

end GeneralMinimizationProblem
