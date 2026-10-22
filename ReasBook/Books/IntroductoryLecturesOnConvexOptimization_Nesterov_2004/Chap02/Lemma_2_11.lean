/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Lemma 2.11 is a recall-only source-facing item in the convex-sublevel-set domain.

Sampled owner-style declarations:
* `ConvexOn.convex_le`, the owner theorem for convex sublevel sets on an ambient set;
* `ConvexOn.convex_lt`, the open-sublevel analogue in the same owner API;
* `Convex.quasiconvexOn_of_convex_le`, showing that convex sublevel sets are the canonical route
  to quasiconvexity;
* `convex_euclidean_posSemidef_quadratic_sublevelSet` in `Chap02/Exmaple_2_18_1.lean`, a
  downstream chapter use that already calls `ConvexOn.convex_le` directly.

Best owner abstraction:
* `ConvexOn ℝ Set.univ f`.

Primitive data:
* a function `f : ℝⁿ → ℝ`;
* the owner hypothesis `ConvexOn ℝ Set.univ f`.

Derived API:
* convexity of the sublevel set `{x | f x ≤ β}`.

Source/core/bridge triage:
* source-facing: the textbook whole-space sublevel-set convexity lemma;
* core/canonical: the owner predicate `ConvexOn ℝ Set.univ f`;
* bridge/view: `ConvexOn.convex_le`, which produces the sublevel-set convexity statement from the
  owner predicate.

So this file stays as direct canonical recall/use. It intentionally adds no parallel wrapper
theorem, and downstream files should use `ConvexOn.convex_le` directly.
-/

recall ConvexOn.convex_le
