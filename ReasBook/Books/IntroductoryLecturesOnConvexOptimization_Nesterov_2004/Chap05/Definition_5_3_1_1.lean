/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 5.3.1.1 is a source-facing recall in the chapter's central-path / interior-point
domain.

Primary domain:
- central paths for barrier-penalized linear minimization on a feasible set in a real
  inner-product space.

Sampled owner-style declarations:
- `centralPathPenaltyObjective` in `Definition_5_3_6_1`, the chapter owner for the penalty
  objective `x ↦ t ⟪c, x⟫ + F x`;
- `centralPathPenaltyObjective_apply`, the defining evaluation theorem for that owner;
- `IsCentralPath` in `Definition_5_3_6_1`, the chapter owner predicate for central paths;
- `isCentralPath_iff`, the companion pointwise minimizer expansion on the canonical `IsMinOn`
  owner.

Best owner abstraction:
- source-facing/core: `centralPathPenaltyObjective` and `IsCentralPath`;
- bridge/view: `centralPathPenaltyObjective_apply` and `isCentralPath_iff`.

Primitive data:
- `dom : Set E`
- `c : E`
- `f : E → ℝ`
- `xStar : Set.Ici (0 : ℝ) → dom`

Derived API:
- the penalty formula
  `centralPathPenaltyObjective c f t x = (t : ℝ) * inner ℝ c x + f x`;
- the pointwise minimizer expansion of `IsCentralPath dom c f xStar`.

Source/core/bridge triage:
- source-facing: the textbook penalty objective and central-path predicate of Definition 5.3.1.1;
- core/canonical: the existing Chapter 5 owner declarations in `Definition_5_3_6_1`;
- bridge/view: the evaluation and `iff` companion theorems.

The previous version duplicated those owner declarations verbatim, creating a second public copy
of the same central-path surface. This file now recalls the existing owner declarations directly
instead of maintaining parallel local definitions. -/

recall centralPathPenaltyObjective
recall centralPathPenaltyObjective_apply
recall IsCentralPath
recall isCentralPath_iff
