/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_29

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Theorem 3.36 lies in the chapter's unrestricted minimax / saddle-value domain.

Primary domain:
- unrestricted minimax for a parametric payoff, already organized in the project around the
  set-based saddle-point and pointwise-supremum owners.

Relevant sampled declarations:
- `minimax_eq_of_unique_slice_argmin_and_attained_dual_max`
- `isSaddlePointOn_of_unique_slice_argmin_and_attained_dual_max`
- `isMinOn_objective_of_unique_slice_argmin_and_attained_dual_max`
- `pointwiseSupremumOn`

Best owner abstraction:
- source-facing: this numbered recall surface;
- core/canonical: the chapter owner
  `minimax_eq_of_unique_slice_argmin_and_attained_dual_max` from
  `Theorem_3_1_29`, phrased through `pointwiseSupremumOn`, `IsSaddlePointOn`, `IsMinOn`, and
  `IsMaxOn`;
- bridge/view: the unrestricted case is the specialization `P = Set.univ`, `S = Set.univ`.

Primitive data:
- none in this file; the owner theorem already carries the full mathematical data.

Derived API:
- the recalled minimax theorem, together with the saddle-point and primal-minimizer companions in
  `Theorem_3_1_29`.

This file no longer introduces a second public lower-envelope theorem or companion bridge lemmas.
The same textbook item is already canonicalized upstream in `Theorem_3_1_29`, so the correct
surface here is direct reuse of that owner rather than a parallel `sInf (Set.range ...)` wrapper.
-/

recall minimax_eq_of_unique_slice_argmin_and_attained_dual_max

end
