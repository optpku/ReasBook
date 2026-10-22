/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_7

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.7 lies in the chapter's extended-valued convex-analysis / subdifferential-calculus
domain.

Sampled owner-style declarations:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain
  and finite-value representative;
- `IsSubgradientAt` and `subdifferential` in `Definition_3_1_5`, the chapter owners for
  extended-valued subgradients;
- `subdifferential_eq_singleton_gradient` in `Lemma_3_1_7`, already stated on those owner
  abstractions.

Best owner abstraction:
- `subdifferential_eq_singleton_gradient` from `Lemma_3_1_7`.

Primitive data:
- none in this file; the theorem already lives upstream on the canonical owner surface.

Derived API:
- this recall-only source-facing entry point.

Source/core/bridge triage:
- source-facing: Lemma 3.7's singleton-subdifferential statement;
- core/canonical: `dom`, `withTopRealPart`, and `subdifferential`;
- bridge/view: this recall surface.

The previous file duplicated the effective-domain, finite-real-part, convexity, subgradient, and
subdifferential owners even though the exact theorem already exists in `Lemma_3_1_7`. This
refinement removes that parallel local API and reuses the canonical chapter theorem directly.
-/

recall subdifferential_eq_singleton_gradient
