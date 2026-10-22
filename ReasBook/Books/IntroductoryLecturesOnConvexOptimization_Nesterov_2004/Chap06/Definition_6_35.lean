/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_34

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 6.35 [Chapter6_1.json:78] lies in Chapter 6's scalar smoothness-parameter domain.

Sampled owner declarations:
* `smoothness_parameters`, the chapter owner for the ordered pair `(μ₁, μ₂)`;
* `smoothness_parameters_fst` and `smoothness_parameters_snd`, the projection bridges recovering
  the two displayed formulas.

Best owner abstraction:
* source-facing: the ordered pair `(μ₁, μ₂)` attached to `D₁`, `D₂`, `‖A‖_{1,2}`, `λ₁`, and `λ₂`;
* core/canonical: the existing pair-valued owner `smoothness_parameters`;
* bridge/view: the projection formulas for `μ₁` and `μ₂`.

This item adds no new mathematical owner beyond the scalar parametrization already defined in
`Definition_6_34`, so the correct statement-stage surface here is a direct recall rather than a
second wrapper definition. -/

/- Definition 6.35 [Chapter6_1.json:78]: the smoothness parameters are the ordered pair
`(μ₁, μ₂)` with
`μ₁ = λ₁ ‖A‖_{1,2} √(D₂ / D₁)` and `μ₂ = λ₂ ‖A‖_{1,2} √(D₁ / D₂)`. -/
recall smoothness_parameters

recall smoothness_parameters_fst

recall smoothness_parameters_snd
