/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_12

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 3.13 is a recall-only bridge in the chapter's one-dimensional
positive-part/subdifferential domain.

Primary domain:
- the subdifferential of the real positive-part function.

Sampled owner-style declarations:
- `posPart` and `posPart_def`, the canonical positive-part owner and its `max` description;
- `subdifferential` and `mem_subdifferential_iff`, the chapter owner API for extended-valued
  subgradients;
- `real_posPart_subdifferential_at_zero_eq_Icc` in `Proposition_3_12`, the earlier canonical
  chapter theorem for this fact.

Best owner abstraction:
- `real_posPart_subdifferential_at_zero_eq_Icc`.

Primitive data:
- none in this file; the statement is already owned upstream.

Derived API:
- this recall-only textbook entry point.

Source/core/bridge triage:
- source-facing: the textbook claim for `x ↦ max x 0`;
- core/canonical: `real_posPart_subdifferential_at_zero_eq_Icc`;
- bridge/view: this recall surface.

The previous version kept a second public theorem with the same mathematical content as
`real_posPart_subdifferential_at_zero_eq_Icc`. This refinement removes that duplicate wheel and
reuses the earlier chapter owner directly. -/

/- Proposition 3.13: for `f(x) = (x)_+ = max x 0`, the subdifferential at `0` is exactly the
interval `[0, 1]`. -/
recall real_posPart_subdifferential_at_zero_eq_Icc
