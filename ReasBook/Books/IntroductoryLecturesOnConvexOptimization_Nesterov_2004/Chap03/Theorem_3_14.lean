/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_12

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.14 lies in the chapter's convex directional-derivative domain.

Sampled owner-style declarations:
- `HasDirectionalDerivAt` in
  `Nesterov.Chap03.Definition_3_1_3_1`, the source-facing owner for one-sided directional
  derivatives of extended-real-valued functions;
- `exists_tendsto_right_directionalSlope_of_convexOn_of_mem_interior_effectiveDomain` in
  `Nesterov.Chap03.Theorem_3_1_12`, the canonical secant-slope existence theorem for convex
  `WithTop ℝ`-valued functions at interior points;
- `ConvexOn.slope_mono` and `bddBelow_slope_lt_of_mem_interior` in mathlib
  `Mathlib/Analysis/Convex/Deriv.lean`, the one-variable slope monotonicity and interior-point
  boundedness lemmas underlying the owner theorem.

Best owner abstraction:
- source-facing: Theorem 3.14's one-sided directional-slope limit statement at an interior point
  of the effective domain;
- core/canonical: the stronger chapter theorem
  `exists_tendsto_right_directionalSlope_of_convexOn_of_mem_interior_effectiveDomain`;
- bridge/view: the `EReal`-valued limit presentation obtained by coercing the owner theorem's
  finite real limit.

Primitive data:
- a convexity witness
  `hf : ConvexOn ℝ {y : E | f y < ⊤} (fun y ↦ (f y).untopD 0)`;
- an interior point `hx : x ∈ interior {y : E | f y < ⊤}`.

Derived API:
- the eventual finiteness of the ray `α ↦ x + α • p`, already bundled in the owner theorem;
- the finite real right limit of the secant slopes, also bundled in the owner theorem;
- the weaker `EReal`-valued limit form stated by the textbook item.

The previous file reintroduced a second public theorem name for a weaker consequence of the
already-canonical chapter theorem in `Theorem_3_1_12`. Since the stronger owner theorem is the
correct reusable API and there are no direct downstream uses of the duplicate local name, this file
now recalls the owner theorem directly instead of preserving a parallel wrapper.
-/

recall exists_tendsto_right_directionalSlope_of_convexOn_of_mem_interior_effectiveDomain
