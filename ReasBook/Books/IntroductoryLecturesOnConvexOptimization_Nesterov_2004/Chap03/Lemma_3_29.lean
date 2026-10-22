/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_29

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin
open scoped NormalCone
open scoped WithTopConvexAnalysis

/- Lemma 3.29 lies in the chapter's constrained convex minimization / common-certificate domain.

Mandatory domain-style sampling before refinement:
- `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical owner
  for constrained minimizers;
- `commonRegularSubdifferential` and `mem_commonRegularSubdifferential_iff` in
  `Definition_3_1_5_4`, the chapter owner for common subdifferentials;
- `normalCone` and `mem_normalCone_iff` in `Definition_3_22`, the pointwise normal-cone owner;
- `subgradient_mem_commonRegularSubdifferential_commonNormalCone_of_mem_constrainedArgmin` in
  `Theorem_3_29`, the owner theorem already proving the propagated certificate statement.

Best owner abstraction:
- the constrained minimizer set `argmin[Q] f`;
- the common regular subdifferential `∂̂ f(X)`;
- the common normal cone `NormalCone.common X`.

Primitive data:
- a feasible set `Q`;
- a real-valued objective `f`;
- an optimal point `xStar`;
- a subgradient certificate `gStar`.

Derived API:
- the source-facing propagated pairing certificate on `argmin[Q] f`;
- the owner-level common-normal-cone corollary.

Source/core/bridge triage:
- source-facing:
  `subgradient_mem_commonRegularSubdifferential_and_nonneg_pairing_of_mem_constrainedArgmin`;
- core/canonical:
  `subgradient_mem_commonRegularSubdifferential_commonNormalCone_of_mem_constrainedArgmin`;
- bridge/view:
  `NormalCone.mem_common_iff_nonneg_pairing` from `Theorem_3_29`.

The previous file imported the nonexistent module `Theorem_3_2_4` and wandered into the
approximate-Lagrange-multiplier domain. The actual Chapter 3 owner declarations already live in
`Theorem_3_29`, so this file is recall-only and reuses that canonical surface directly instead of
keeping a parallel local statement. -/

/- Lemma 3.29, pairing form: the propagated certificate belongs to the common regular
subdifferential and satisfies the normal-cone pairing inequalities on the whole constrained
minimizer set. -/
recall subgradient_mem_commonRegularSubdifferential_and_nonneg_pairing_of_mem_constrainedArgmin

/- Owner-level corollary: the same propagated certificate belongs to the common normal cone of the
constrained minimizer set. -/
recall subgradient_mem_commonRegularSubdifferential_commonNormalCone_of_mem_constrainedArgmin
