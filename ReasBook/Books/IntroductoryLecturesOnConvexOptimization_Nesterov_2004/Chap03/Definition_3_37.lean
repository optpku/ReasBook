/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_1

-- Declarations for this item will be appended below by the statement pipeline.

/-
Definition 3.37 lies in the cutting-plane localization-measure domain.

Primary mathematical domain:
- subgradient-based localization radii around a reference point in finite-dimensional Euclidean
  cutting-plane analysis.

Sampled owner-style declarations:
- `subgradientLocalizationMeasure` in `Lemma_3_2_1`, the chapter owner for `v_f(xBar; x)`
- `subgradientLocalizationMeasure_eq_zero_of_eq_zero` in `Lemma_3_2_1`, the owner-level
  zero-branch simplification
- `subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero` in `Lemma_3_2_1`, the owner-level
  nonzero-branch simplification
- `sub_le_pointwiseGrowthFunction_of_localizationMeasure` in `Lemma_3_2_1`, the first comparison
  theorem built from the same owner

Best owner abstraction for this file:
- `subgradientLocalizationMeasure`

Primitive data:
- a reference point `xBar`
- a chosen subgradient selection `g`
- an evaluation point `x`

Derived API:
- the zero-case simplification theorem
  `subgradientLocalizationMeasure_eq_zero_of_eq_zero`
- the nonzero-case simplification theorem
  `subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero`
- the comparison
  `sub_le_pointwiseGrowthFunction_of_localizationMeasure`

Source/core/bridge triage:
- source-facing: the pointwise localization measure `subgradientLocalizationMeasure g xBar x`
- core/canonical: `subgradientLocalizationMeasure`
- bridge/view: the zero/nonzero branch simplifications and the growth-function comparison obtained
  by unfolding the owner

The owner declaration `subgradientLocalizationMeasure` in `Lemma_3_2_1` already carries the exact
mathematical content of Definition 3.37. This file therefore recalls that owner directly instead
of keeping a parallel local copy. The branch simplification theorems stay with the owner file
rather than being re-recalled from this definition-only item.
-/

recall subgradientLocalizationMeasure
