/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 3.1.1.1 lies in the chapter's extended-real effective-epigraph closedness domain.

Primary domain:
- closedness of effective epigraphs of `EReal`-valued functions on topological spaces, expressed
  through continuity of the finite real part on the effective domain.

Sampled owner-style declarations:
- chapter `dom f` and `extendedRealRealPart f` from `Definition_3_1_1_3`, the canonical
  finite-value owner/bridge vocabulary in this domain;
- `isClosed_effectiveEpigraph_of_continuousOn_of_isClosed_dom` in `Proposition_3_2`, the
  source-facing chapter theorem on `effectiveEpigraph f`;
- `isClosed_effectiveEpigraph_of_lowerSemicontinuousOn_of_isClosed_dom` in `Proposition_3_2`,
  the stronger companion obtained by weakening continuity to lower semicontinuity;
- mathlib `ContinuousOn.lowerSemicontinuousOn`, the canonical bridge from the source-facing
  continuity statement to the companion strengthening;
- mathlib `LowerSemicontinuousOn.isClosed_re_epigraph`, the canonical real-epigraph closedness
  owner used by the chapter theorem.

Best owner abstraction:
- the existing chapter theorem
  `isClosed_effectiveEpigraph_of_continuousOn_of_isClosed_dom`.

Primitive data:
- the `EReal`-valued function `f`;
- continuity of `extendedRealRealPart f` on `dom f`;
- closedness of `dom f`.

Derived API:
- closedness of the effective epigraph `{p : X × ℝ | p.1 ∈ dom f ∧ f p.1 ≤ p.2}`.
- companion strengthening under lower semicontinuity on `dom f`.

Source/core/bridge triage:
- source-facing: this effective-epigraph closedness proposition;
- core/canonical: mathlib lower-semicontinuity / `isClosed_re_epigraph`;
- bridge/view: the chapter theorem
  `isClosed_effectiveEpigraph_of_continuousOn_of_isClosed_dom`.

This file therefore remains recall-only: the proposition-level statement already exists upstream in
the minimal chapter closure with the correct canonical `dom f` owner surface, so introducing a
second local theorem here would only recreate the duplicate-wheel problem. -/

recall isClosed_effectiveEpigraph_of_continuousOn_of_isClosed_dom
