/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_12

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.12 lies in the chapter's weighted-sum / subdifferential calculus for closed convex
`WithTop ℝ`-valued functions on the intrinsic ambient spaces already used by the chapter owners.

Relevant sampled declarations in this domain:
- `withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos` from `Lemma_3_1_12`
- `ClosedConvexFunction.nonneg_weighted_add` from `Lemma_3_1_12`
- `interior_effectiveDomain_nonneg_weighted_add_eq_of_pos` from `Lemma_3_1_12`
- `subdifferential_nonneg_weighted_add_eq_of_pos` from `Lemma_3_1_12`
- `withTopEffectiveDomain` from `Definition_3_3`
- `ClosedConvexFunction` from `Definition_3_1_1_5`
- `subdifferential` from `Definition_3_1_5`

Best owner abstraction:
- the canonical pointwise weighted sum
  `((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂)`
- the ambient effective-domain, closed-convex, and subdifferential notions remain owned by the
  earlier chapter files sampled above
- this file is therefore a bridge/view recalling the weighted-sum theorems stated directly on that
  canonical owner

Primitive data:
- none in this recall file; the imported owner surface already carries the only primitive
  mathematical inputs, namely the scalars `α₁`, `α₂` and the summands `f₁`, `f₂`

Derived API:
- `withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos`
- `ClosedConvexFunction.nonneg_weighted_add`
- `interior_effectiveDomain_nonneg_weighted_add_eq_of_pos`
- `subdifferential_nonneg_weighted_add_eq_of_pos`

Source/core/bridge triage:
- source-facing: the three weighted-sum consequences in Lemma 3.12, now stated on the canonical
  pointwise weighted sum
- core/canonical: `withTopEffectiveDomain`, `ClosedConvexFunction`, `subdifferential`
- bridge/view: the positive-weight effective-domain identity and this recall-only file

This bridge now recalls the weighted-sum conclusions directly on the canonical pointwise weighted
sum. The incorrect auxiliary wrapper has been removed, so the exported surface no longer shrinks
domains at zero weights. -/

recall withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos

recall ClosedConvexFunction.nonneg_weighted_add

recall interior_effectiveDomain_nonneg_weighted_add_eq_of_pos

recall subdifferential_nonneg_weighted_add_eq_of_pos
