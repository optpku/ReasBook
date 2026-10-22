/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_26

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.32: (Karush--Kuhn--Tucker) under convexity, differentiability, and a Slater point
for the inequality constraints on `Q`, a point `x*` solves
`min {f₀(x) | x ∈ Q, fᵢ(x) ≤ 0}` if and only if there exists a nonnegative multiplier vector
whose Lagrangian gradient pairing is nonnegative on `Q` and which satisfies complementary
slackness at `x*`.

This numbered item is already formalized on the canonical Chapter 3 owner surface in
`isMinOn_iff_exists_karush_kuhn_tucker_multiplier`, so this file reuses that theorem directly
instead of introducing a parallel local KKT API.
-/
recall isMinOn_iff_exists_karush_kuhn_tucker_multiplier
