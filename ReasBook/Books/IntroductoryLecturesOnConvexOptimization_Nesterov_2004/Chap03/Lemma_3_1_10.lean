/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_10

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.1.10 is a recall-only bridge in the chapter's extended-valued convex-analysis /
continuous-subgradient-selection domain.

Primary domain:
- convex analysis of `WithTop ℝ`-valued functions on real inner-product spaces, with a continuous
  local selection of pointwise subgradients.

Relevant sampled declarations in this domain:
- `subdifferential` from `Definition_3_1_5`, the chapter owner for extended-valued subgradients;
- `withTopRealPart` from `Definition_3_3`, the canonical real-valued representative on `dom f`;
- `HasGradientAt`, the canonical gradient owner for differentiability with a specified gradient;
- `hasGradientAt_withTopRealPart_of_continuous_subgradient_selection` from `Lemma_3_10`, the
  exact upstream owner theorem for this source item.

Best owner abstraction:
- the exact upstream owner theorem
  `hasGradientAt_withTopRealPart_of_continuous_subgradient_selection` from `Lemma_3_10`.

Primitive data:
- none in this recall file; the actual source-facing assumptions already live in `Lemma_3_10`.

Derived API recalled here:
- the owner `HasGradientAt` conclusion for the selected subgradient;
- the derived differentiability consequence;
- the derived gradient-identification consequence.

Source/core/bridge triage:
- source-facing: Lemma 3.1.10's differentiability statement from a continuous local subgradient
  selection;
- core/canonical: `subdifferential`, `withTopRealPart`, and `HasGradientAt`;
- bridge/view: the derived `DifferentiableAt` and gradient-equality consequences.

The previous version drifted into the unrelated finite pointwise-supremum / active-set API from
`Lemma_3_1_13`. This file instead reuses the actual `Lemma_3_10` owner family directly and keeps
the later numbered item aligned with its true source mathematics.
-/

recall hasGradientAt_withTopRealPart_of_continuous_subgradient_selection
recall differentiableAt_withTopRealPart_of_continuous_subgradient_selection
recall gradient_eq_of_continuous_subgradient_selection
