/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_1

-- Declarations for this item will be appended below by the statement pipeline.

/-
Definition 3.38 lies in the Chapter 3 pointwise-growth / local-modulus domain.

Primary domain:
- supremal growth profiles of a real-valued function around a base point on `ℝⁿ`.

Sampled owner-style declarations:
- `pointwiseGrowthFunction` in `Lemma_3_2_1`, the chapter owner for `ω_f(xBar; t)`
- `pointwiseGrowthFunction_eq_zero_of_neg` in `Lemma_3_2_1`, the owner-level negative-radius
  branch simplification
- `sub_le_pointwiseGrowthFunction_of_localizationMeasure` in `Lemma_3_2_1`, the first comparison
  theorem built from the same owner
- `pointwiseGrowthFunction_monotone` in `Proposition_3_34`, the radius-monotonicity theorem for
  the same owner profile

Best owner abstraction:
- `pointwiseGrowthFunction`

Primitive data:
- a real-valued function `f`
- a base point `xBar`
- a radius parameter `t`

Derived API:
- the owner-level negative-radius simplification `pointwiseGrowthFunction_eq_zero_of_neg`
- the localization-measure comparison
  `sub_le_pointwiseGrowthFunction_of_localizationMeasure`
- the monotonicity and radius-evaluation consequences developed downstream in
  `Proposition_3_34`

Source/core/bridge triage:
- source-facing: the textbook growth function `ω_f(xBar; t)`
- core/canonical: `pointwiseGrowthFunction`
- bridge/view: the branch simplifications and comparison lemmas obtained by unfolding the owner

The owner declaration `pointwiseGrowthFunction` in `Lemma_3_2_1` already carries the exact
mathematical content of Definition 3.38. This file therefore recalls that owner directly instead
of keeping a parallel local copy such as `pointwise_growth_function`. The negative-radius branch
theorem stays with the owner file instead of being re-exported from this definition-only recall.
-/

recall pointwiseGrowthFunction
