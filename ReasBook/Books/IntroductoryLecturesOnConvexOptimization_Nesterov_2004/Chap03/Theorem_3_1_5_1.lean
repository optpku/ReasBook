/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_15

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.1.5.1 is a recall-only surface in the chapter's extended-valued convex-
subdifferential domain.

Primary domain:
- convex analysis of `ℝ ∪ {+∞}`-valued functions on Euclidean space.

Sampled owner-style declarations:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain
  and finite-value representative;
- `subdifferential` in `Definition_3_1_5`, the chapter owner for extended-valued subgradient
  sets;
- `subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior` in
  `Theorem_3_1_15`, the canonical chapter theorem on this owner surface.

Best owner abstraction:
- `subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior`.

Primitive data:
- none in this file; the theorem and its owner-level hypotheses already live upstream.

Derived API:
- this recall-only source-facing entry point.

Source/core/bridge triage:
- source-facing: Theorem 3.1.5.1's nonempty-and-bounded subdifferential statement;
- core/canonical: the upstream theorem in `Theorem_3_1_15` on the chapter owners
  `dom`, `withTopRealPart`, and `subdifferential`;
- bridge/view: this recall surface.

The previous file kept a second theorem stub with the same statement as the canonical upstream
theorem. This file now reuses that theorem directly instead of maintaining a parallel copy.
-/

recall subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
