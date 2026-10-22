/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 3.1.1.6 is a recall-only item in the seminorm-geometry domain.

Layer targeted by this refinement:
- source-facing recall of the core/canonical owner closed-ball API for seminorms

Primary domain:
- closed balls attached to seminorms.

Sampled owner-style declarations:
- `Seminorm.closedBall`
- `Seminorm.mem_closedBall`
- `Seminorm.mem_closedBall_zero`
- `Seminorm.closedBall_zero_eq`

Primitive data:
- a seminorm `p : Seminorm ℝ E`
- a center `x₀ : E`
- a radius `r : ℝ`

Derived API:
- `Seminorm.mem_closedBall` gives the set-builder characterization
  `x ∈ p.closedBall x₀ r ↔ p (x - x₀) ≤ r`.

Source/core/bridge triage:
- source-facing: the textbook closed ball attached to a seminorm
- core/canonical: `Seminorm.closedBall`
- bridge/view: the defining membership lemma `Seminorm.mem_closedBall`

This file therefore keeps only the general owner declaration and its defining bridge view.
Downstream unit-ball files should use the same owner declaration directly and recall the zero-center
specializations there.
-/

recall Seminorm.closedBall
recall Seminorm.mem_closedBall
