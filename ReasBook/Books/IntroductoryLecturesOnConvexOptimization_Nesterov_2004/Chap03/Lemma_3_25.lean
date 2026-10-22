/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.25 lies in the chapter's subgradient-localization / pointwise-growth domain.

Primary mathematical domain:
- real-valued convex analysis on `ℝⁿ`, organized around subgradient-based localization radii and
  growth functions.

Sampled owner-style declarations:
- `IsSubgradientAt` in `Definition_3_1_5`, the chapter owner predicate for subgradients via the
  canonical `WithTop`-valued formulation;
- `subgradientLocalizationMeasure` in `Lemma_3_2_1`, with source-facing surface `v[g; xBar] x`
  for the localization radius attached to a chosen subgradient selection;
- `pointwiseGrowthFunction` in `Lemma_3_2_1`, with source-facing surface `ω[f; xBar] t` for the
  supremal ball-growth profile;
- `sub_le_lipschitz_mul_max_localizationMeasure` in `Lemma_3_2_1`, the owner theorem for the
  Lipschitz growth bound.

Best owner abstraction:
- `subgradientLocalizationMeasure`
- `pointwiseGrowthFunction`
- the owner comparison theorems built from them in `Lemma_3_2_1`

Primitive data:
- a real-valued function `f : V → ℝ` on a real inner product space;
- a chosen subgradient selection `g : V → V`;
- the base point `xBar` and evaluation point `x`.

Derived API:
- the growth comparison
  `sub_le_pointwiseGrowthFunction_of_localizationMeasure`;
- the Lipschitz refinement
  `sub_le_lipschitz_mul_max_localizationMeasure`.

Source/core/bridge triage:
- source-facing: Lemma 3.25's comparison of `f x - f xBar` with the canonical growth function and
  its Lipschitz specialization;
- core/canonical: `IsSubgradientAt`, `subgradientLocalizationMeasure`, and
  `pointwiseGrowthFunction`;
- bridge/view: none beyond the coercion `fun y ↦ (f y : WithTop ℝ)` already absorbed by the owner
  theorems.

The previous version duplicated a real-valued subgradient predicate, its subdifferential, the
localization measure, the growth function, and two theorem wrappers carrying an unused convexity
hypothesis. The chapter already centers this domain on `Lemma_3_2_1`, so this file now recalls the
owner theorems directly instead of keeping a second local API surface.
-/

recall sub_le_pointwiseGrowthFunction_of_localizationMeasure

recall sub_le_lipschitz_mul_max_localizationMeasure
