/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_8_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 5.4.8.8 is a recall-only item in the Chapter 5 exponential-epigraph barrier domain.

Primary domain:
- logarithmic barriers for the exponential epigraph in `ℝ × ℝ`.

Sampled owner-style declarations:
- `exponentialEpigraphBarrierF2` from `Theorem_5_4_8_3`
- `exponentialEpigraphBarrierF2_apply` from `Theorem_5_4_8_3`
- `exponentialEpigraphQ2` from `Theorem_5_4_8_3`
- `epigraphLogBarrier` from `Theorem_5_3_5`

Best owner abstraction:
- the existing chapter source-facing owner `exponentialEpigraphBarrierF2`

Primitive data:
- none; this numbered item introduces no new primitive object beyond the existing owner.

Derived API:
- the owner declaration `exponentialEpigraphBarrierF2`
- the defining evaluation lemma `exponentialEpigraphBarrierF2_apply`

Source/core/bridge triage:
- source-facing: the textbook function `F₂(x, t) = -log t - log (log t - x)`
- core/canonical: `exponentialEpigraphBarrierF2`
- bridge/view: the evaluation theorem `exponentialEpigraphBarrierF2_apply`

The previous version introduced a second public owner `separableLogBarrierF2` for exactly the
same function already exposed upstream. This file now reuses the existing chapter owner directly,
in line with the chapter's recall-only pattern for numbered items that add no new API. -/

/- Definition 5.4.8.8 recalls the existing chapter owner for the textbook barrier `F₂`. -/
recall exponentialEpigraphBarrierF2 : ℝ × ℝ → ℝ

/- The textbook coordinate formula is recalled through the canonical companion theorem. -/
recall exponentialEpigraphBarrierF2_apply (x t : ℝ) :
    exponentialEpigraphBarrierF2 (x, t) = -Real.log t - Real.log (Real.log t - x)
