/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_9

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.1.9 lies in the product-space extended-valued subdifferential domain.

Primary domain:
- convex analysis of `WithTop ℝ`-valued functions on intrinsic `L²` products of real
  inner-product spaces.

Sampled owner-style declarations:
- `subdifferential` in `Definition_3_1_5`, the chapter owner for extended-valued subgradients;
- `partialGradientFst` in `Lemma_3_9`, the source-facing first-slice gradient owner;
- `partialSubdifferentialSnd` in `Lemma_3_9`, the source-facing second-slice subdifferential
  owner;
- `subdifferential_eq_image_partialGradientFst_partialSubdifferentialSnd_of_nhds` in
  `Lemma_3_9`, the exact upstream neighborhood-form theorem for this source fact.

Best owner abstraction:
- the exact upstream theorem
  `subdifferential_eq_image_partialGradientFst_partialSubdifferentialSnd_of_nhds`
  from `Lemma_3_9`, already stated on the canonical ambient owner `subdifferential`.

Primitive data:
- none in this file; the source-facing slice owners and the theorem already live upstream.

Derived API:
- this recall-only source-facing entry point.

Source/core/bridge triage:
- source-facing: Lemma 3.1.9's product-space subdifferential formula;
- core/canonical: `subdifferential`;
- bridge/view: the neighborhood-form theorem in `Lemma_3_9`.

The previous version introduced a second public theorem shell with a weaker linewise continuity
hypothesis than the canonical owner theorem in `Lemma_3_9`. Since the exact source fact already
lives upstream on the correct owner surface, this file should be recall-only and should reuse that
theorem directly rather than maintain a semantically shifted parallel wrapper.
-/

/- Lemma 3.1.9 is the upstream neighborhood-form theorem
`subdifferential_eq_image_partialGradientFst_partialSubdifferentialSnd_of_nhds` from
`Lemma_3_9`. -/

recall subdifferential_eq_image_partialGradientFst_partialSubdifferentialSnd_of_nhds
