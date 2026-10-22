/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_12

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 3.1.5.1 lies in the chapter's real positive-part / subdifferential domain.

Primary domain:
- the one-dimensional subdifferential of the positive-part function.

Relevant owner-style declarations sampled before refinement:
- `posPart` and `posPart_def`, the canonical positive-part owner and its `max` specialization;
- `real_posPart_subdifferential_at_zero_eq_Icc` in `Proposition_3_12`, the earlier chapter theorem
  with the exact source-facing interface;
- the recall-only bridge in `Proposition_3_13`, which now reuses that owner directly.

Best owner abstraction:
- `real_posPart_subdifferential_at_zero_eq_Icc`.

Primitive data:
- none in this file; the statement is already completely owned upstream.

Derived API:
- this recall-only bridge for the numbered textbook item.

Source/core/bridge triage:
- source-facing: the textbook claim identifying the subdifferential of `x ↦ max x 0` at `0`;
- core/canonical: the earlier chapter theorem `real_posPart_subdifferential_at_zero_eq_Icc`;
- bridge/view: this file only, which recalls that owner theorem instead of exporting a third
  parallel theorem shell.

The previous version duplicated an exact theorem already present upstream. This refinement removes
that duplicate wheel and reuses the earlier chapter owner directly. -/

/- Proposition 3.1.5.1: for the real positive-part function `x ↦ max x 0`, the set of real
numbers `g` satisfying the global affine lower-support inequality
`max x 0 ≥ max 0 0 + g * (x - 0)` for every `x` is exactly the interval `[0, 1]`. -/
recall real_posPart_subdifferential_at_zero_eq_Icc
