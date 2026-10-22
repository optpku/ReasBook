/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 3.14 is a recall-only specialization in the chapter's positive-part domain.

Primary domain:
- positive-part operations in ordered additive algebra.

Relevant owner-style declarations sampled before refinement:
- `posPart`
- `posPart_def`
- `posPart_eq_ite`

Best owner abstraction:
- the canonical owner `posPart`, specialized to `ℝ`

Primitive data:
- none beyond the real input variable; the owner map already exists upstream

Derived API:
- the specialization `ℝ → ℝ`
- the pointwise bridge `x⁺ = max x 0`

Source/core/bridge triage:
- source-facing: the textbook real function `x ↦ (x)_+`
- core/canonical: `posPart`
- bridge/view: `posPart_def` specialized to `ℝ`

`Definition_3_1_5_2` already recalls the positive-part owner together with its canonical formulas.
This file therefore deletes the duplicate wrapper `realPosPart` and its parallel bridge theorem,
and keeps Definition 3.14 as the direct real specialization of the existing owner. -/

/- Definition 3.14: the textbook real positive-part function `x ↦ (x)_+` is the real
specialization of the canonical owner `posPart`. -/
#check ((·⁺) : ℝ → ℝ)

/- Pointwise, the real specialization is `x ↦ max x 0`. -/
#check (posPart_def : ∀ x : ℝ, x⁺ = max x 0)
