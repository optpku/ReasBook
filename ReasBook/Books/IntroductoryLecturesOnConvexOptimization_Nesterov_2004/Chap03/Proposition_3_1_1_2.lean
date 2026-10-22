/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 3.1.1.2 lies in the chapter's real convex-analysis / epigraph domain.

Primary domain:
- the epigraph of the absolute value function on `ℝ` and its half-space description in `ℝ × ℝ`.

Sampled owner-style declarations:
- project `abs_convexOn_univ` in `Proposition_3_3`, which owns the convexity of `x ↦ |x|`;
- project `abs_epigraph_isClosed` in `Proposition_3_3`, which owns the closedness of the same
  epigraph;
- project `abs_epigraph_eq_inter_halfspaces` in `Proposition_3_3`, which already has the exact
  textbook set-theoretic statement for this item;
- mathlib `ConvexOn.convex_epigraph`, the canonical ambient epigraph-convexity owner in this
  domain.

Best owner abstraction:
- the existing chapter theorem `abs_epigraph_eq_inter_halfspaces`.

Primitive data:
- none locally; the full mathematical statement already exists upstream in the minimal chapter
  closure.

Derived API:
- the supporting convexity and closedness facts in `Proposition_3_3`.

Source/core/bridge triage:
- source-facing: the half-space description of the epigraph of `|x|`;
- core/canonical: the existing chapter theorem `abs_epigraph_eq_inter_halfspaces`;
- bridge/view: the supporting owner facts `abs_convexOn_univ` and `abs_epigraph_isClosed`.

This file is therefore recall-only. Keeping local definitions such as `absEpigraph`,
`upperDiagonalHalfspace`, or renamed theorem shells would be a forbidden duplicate wrapper around
the existing chapter owner.
-/

/- Proposition 3.1.1.2 is the direct recall of the chapter's half-space description of the
epigraph of the absolute value function. -/
recall abs_epigraph_eq_inter_halfspaces
