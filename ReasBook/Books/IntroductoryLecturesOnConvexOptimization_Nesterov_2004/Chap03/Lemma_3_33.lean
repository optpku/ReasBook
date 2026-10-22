/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_1

/- Lemma 3.33 lies in the chapter's level-method scalar-history domain.

Sampled owner declarations:
* `LevelMethodHistory` in `Lemma_3_3_1`, the owner bundle for `(\hat f_k^*, f_k^*)`
* `LevelMethodHistory.gap` in `Lemma_3_3_1`, the canonical gap `δ_k`
* `LevelMethodHistory.levelValue` in `Lemma_3_3_1`, the canonical level value `ℓ_k(α)`
* `LevelMethodHistory.levelValue_ge_approximateOptimalValue_of_intervalMonotonicity` in
  `Lemma_3_3_1`, the exact owner theorem for the interval-monotonicity form of this item

Best owner abstraction:
* source-facing/core owner for this numbered item:
  `LevelMethodHistory.levelValue_ge_approximateOptimalValue_of_intervalMonotonicity`
* core/canonical ambient owner: `LevelMethodHistory`

Primitive data:
* no new primitive data beyond the imported owner theorem

Derived API:
* the direct recall surface for the interval-monotonicity theorem

Source/core/bridge triage:
* source-facing: Lemma 3.33 itself
* core/canonical: the owner theorem already living in `Lemma_3_3_1`
* bridge/view: this recall file

The previous file kept a second declaration with the exact same theorem name and proof body as the
owner-level interval theorem. That was a duplicate wheel. The owner now lives only in
`Lemma_3_3_1`, and this numbered file is reduced to a pure recall surface.
-/

/- Lemma 3.33 is the direct recall of the owner interval-monotonicity theorem. -/
#check LevelMethodHistory.levelValue_ge_approximateOptimalValue_of_intervalMonotonicity
