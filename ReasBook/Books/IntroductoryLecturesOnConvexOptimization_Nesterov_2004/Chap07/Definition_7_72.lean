/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_4_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 7.72 is a bridge/view item in the chapter's semidefinite log-determinant-barrier
domain.

Mandatory domain-style sampling:
- `logDetBarrier` and `logDetBarrier_apply` in `Chap05/Definition_5_4_4_5`, the Chapter 5 owner
  of the semidefinite log-determinant barrier on the strict cone `𝕊^n₊₊`;
- `negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone` in
  `Chap05/Theorem_5_4_4_3`, the Chapter 5 owner theorem recording that the same barrier has
  parameter `ν = n`;
- `Matrix.PosDef`, the canonical matrix-level positive-definite owner behind the strict-cone
  bridge already used upstream.

Best owner abstraction:
- `logDetBarrier`

Primitive data:
- `n : ℕ`

Derived API:
- `logDetBarrier n : 𝕊^n₊₊ → ℝ`
- `logDetBarrier_apply`
- `negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone`

Source/core/bridge triage:
- source-facing: the semidefinite log-determinant barrier together with the parameter statement
  `ν = n`
- core/canonical: `logDetBarrier`
- bridge/view: `logDetBarrier_apply` and the Chapter 5 self-concordance theorem

The barrier, its strict domain, and the parameter statement are already owned upstream in Chapter
5. This file therefore recalls that canonical API directly instead of keeping parallel Chapter 7
copies of the positive-definite subtype, the barrier itself, or the parameter alias. -/

recall logDetBarrier
recall logDetBarrier_apply
recall negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone
