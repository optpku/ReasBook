/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Text_2_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 2.22.1 is recall-only.

The primary domain here is the simple-set estimate-sequence lower bound built from the
projected-gradient owner API on a nonempty closed convex feasible set.

Owner declarations sampled for this refinement:
* `gradientMapping` and `reducedGradient` in `Definition_2_35_1`;
* `gradientMapping_objective_lower_bound` in `Theorem_2_36`;
* `simple_set_phi_star_lower_bound_intermediate` and
  `simple_set_phi_star_lower_bound_of_objective_lower_bound` in `Text_2_1`.

Best owner abstraction:
* the two theorem-level lower bounds in `Text_2_1`, derived from the canonical projected-gradient
  data and the canonical objective lower bound.

Primitive data: the feasible set `Q`, the objective `f`, the iterate data `(y_k, x_k, v_k)`, and
the scalar parameters `(L, α_k, γ_k, γ_{k+1}, φ_k^*, φ_{k+1}^*)`.

Derived API: the projected-gradient point `x_Q(y_k; L)`, the reduced gradient `g_Q(y_k; L)`, and
the two algebraic lower bounds already packaged in `Text_2_1`.

Source/core/bridge triage:
* source-facing: the remark's lower bound obtained after inserting `(2.2.57)` into the
  estimate-sequence update;
* core/canonical: `gradientMapping`, `reducedGradient`, and
  `gradientMapping_objective_lower_bound`;
* bridge/view: the two theorem-level combination steps in `Text_2_1`.

Accordingly, this file adds no parallel local theorem wrappers; downstream use should refer
directly to the owner declarations from `Text_2_1`. -/

recall simple_set_phi_star_lower_bound_intermediate
recall simple_set_phi_star_lower_bound_of_objective_lower_bound
