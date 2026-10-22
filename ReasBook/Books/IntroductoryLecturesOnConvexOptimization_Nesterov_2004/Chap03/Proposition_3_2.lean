/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped ConvexAnalysis

/- Proposition 3.2 lies in the chapter's extended-real epigraph-closedness bridge.

Primary domain:
- closedness of the effective real epigraph of an `EReal`-valued function on a topological space.

Sampled owner-style declarations:
- chapter `dom f` from `Definition_3_1_1_2`, the canonical finite-value owner;
- chapter `effectiveEpigraph f`, `extendedRealRealPart f`, and
  `effectiveEpigraph_eq_epigraph_extendedRealRealPart` from `Definition_3_1_1_3`,
  the canonical owner/bridge surface from `EReal` values to real epigraph inequalities on
  `dom f`;
- mathlib `ContinuousOn.lowerSemicontinuousOn`, the canonical continuity-to-lower-semicontinuity
  bridge;
- mathlib `LowerSemicontinuousOn.isClosed_re_epigraph`, the owner closedness theorem for real
  epigraphs over a closed set.

Best owner abstraction:
- source-facing: the effective epigraph `effectiveEpigraph f`;
- core/canonical: the real epigraph
  `{p : X × ℝ | p.1 ∈ dom f ∧ extendedRealRealPart f p.1 ≤ p.2}` of
  `extendedRealRealPart f` on `dom f`;
- bridge/view: `ContinuousOn.lowerSemicontinuousOn` and
  `effectiveEpigraph_eq_epigraph_extendedRealRealPart`.

Primitive data:
- the `EReal`-valued function `f`;
- continuity of `extendedRealRealPart f` on `dom f`;
- closedness of the chapter owner `dom f`.

Derived API:
- closedness of `effectiveEpigraph f`.
- companion strengthening: the same conclusion under the weaker lower-semicontinuity hypothesis.

Source/core/bridge triage:
- source-facing: the effective-epigraph closedness statement below on `effectiveEpigraph f`
  from continuity on `dom f`;
- core/canonical: `LowerSemicontinuousOn.isClosed_re_epigraph`;
- bridge/view: `dom f`, `extendedRealRealPart f`,
  `ContinuousOn.lowerSemicontinuousOn`, and
  `effectiveEpigraph_eq_epigraph_extendedRealRealPart`.

The source-facing proposition uses continuity of the finite real part on `dom f`. The canonical
owner theorem behind it is the lower-semicontinuous real-epigraph closedness result, so the file
keeps the continuity statement as the main proposition and records the lower-semicontinuity
version only as a strengthening companion.
-/

variable {X : Type u} [TopologicalSpace X]

/-- Proposition 3.2, generalized from the textbook `ℝⁿ` setting: if the finite real part of
`f : X → ℝ ∪ {±∞}` is continuous on its finite-value domain `dom f`, and `dom f` is closed, then
the effective epigraph of `f` is a closed subset of `X × ℝ`. -/
-- Proof sketch: continuity on `dom f` implies lower semicontinuity there. Then
-- `effectiveEpigraph f` is definitionally the real epigraph of `extendedRealRealPart f` over
-- `dom f`, so `LowerSemicontinuousOn.isClosed_re_epigraph` applies and the bridge rewrites the
-- conclusion back to the source-facing effective epigraph.
theorem isClosed_effectiveEpigraph_of_continuousOn_of_isClosed_dom
    {f : X → EReal}
    (hf_cont : ContinuousOn (extendedRealRealPart f) (dom f))
    (hdom_closed : IsClosed (dom f)) :
    IsClosed (effectiveEpigraph f) := by
  simpa [effectiveEpigraph_eq_epigraph_extendedRealRealPart] using
    hf_cont.lowerSemicontinuousOn.isClosed_re_epigraph hdom_closed

/-- Companion strengthening of Proposition 3.2: continuity on `dom f` can be weakened to lower
semicontinuity of the finite real part on `dom f`. -/
theorem isClosed_effectiveEpigraph_of_lowerSemicontinuousOn_of_isClosed_dom
    {f : X → EReal}
    (hf_lower : LowerSemicontinuousOn (extendedRealRealPart f) (dom f))
    (hdom_closed : IsClosed (dom f)) :
    IsClosed (effectiveEpigraph f) := by
  simpa [effectiveEpigraph_eq_epigraph_extendedRealRealPart] using
    hf_lower.isClosed_re_epigraph hdom_closed
