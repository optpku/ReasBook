/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Theorem 5.4.7.15 lies in the same self-concordant-barrier / exponential-transform domain as
Lemma 5.3.1.

Sampled owner-style declarations:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the barrier owner;
* `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div` in `Lemma_5_3_1`, already stated with the
  exact interface required here;
* `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div` in `Lemma_5_3_1`, the numbered
  source-facing characterization built from that owner theorem.

Best owner abstraction:
* `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div`.

Primitive data:
* none in this file beyond the owner theorem's existing parameters.

Derived API:
* this recall-only source-facing entry point.

Source/core/bridge triage:
* source-facing: the textbook statement of Theorem 5.4.7.15;
* core/canonical: `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div`;
* bridge/view: this recall surface.

The previous file duplicated the owner theorem from `Lemma_5_3_1` with the same interface. This
refinement removes that parallel theorem and reuses the canonical owner-level declaration
directly. -/

/- Theorem 5.4.7.15 is `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div`. -/
recall IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div
