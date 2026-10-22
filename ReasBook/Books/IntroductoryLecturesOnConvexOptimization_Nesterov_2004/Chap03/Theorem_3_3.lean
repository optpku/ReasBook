/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Theorem 3.3 lies in the chapter's `WithTop`-valued convex-analysis / effective-epigraph domain.

Sampled owner-style declarations:
- `WithTopConvexAnalysis.effectiveEpigraph`,
  `WithTopConvexAnalysis.effectiveEpigraph_eq_epigraph_withTopRealPart`,
  `dom`, and `withTopRealPart` in `Definition_3_3`, the chapter owner surface and bridge from an
  `ℝ ∪ {+∞}`-valued function to its finite real part and effective epigraph;
- mathlib `convexOn_iff_convex_epigraph`, the core owner equivalence between `ConvexOn` and
  convexity of the ordinary epigraph.

Best owner abstraction:
- source-facing: the effective-epigraph convexity criterion below on
  `WithTopConvexAnalysis.effectiveEpigraph f`;
- core/canonical: `ConvexOn ℝ (dom f) (withTopRealPart f)`;
- bridge/view: `WithTopConvexAnalysis.effectiveEpigraph f`.

Primitive data:
- the chapter owner `dom f`;
- the chapter owner `withTopRealPart f`.

Derived API:
- `WithTopConvexAnalysis.effectiveEpigraph f`;
- `WithTopConvexAnalysis.effectiveEpigraph_eq_epigraph_withTopRealPart`;
- the equivalence below, obtained by reusing `convexOn_iff_convex_epigraph`.

The previous statement duplicated the owner effective-domain set `{x | f x < ⊤}` and the finite
real-part map `x ↦ (f x).untopD 0`. These are already owned upstream by `dom f` and
`withTopRealPart f`. The remaining noncanonical surface was the raw composite
`constrainedEpigraph (dom f) f`, so this file now uses the dedicated owner
`WithTopConvexAnalysis.effectiveEpigraph f` and its upstream bridge to the ordinary epigraph of
`withTopRealPart f`.
-/

open scoped WithTopConvexAnalysis

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]

/-- Theorem 3.3: an `ℝ ∪ {+∞}`-valued function is convex on its effective domain exactly when its
epigraph over that domain is a convex subset of the ambient product space. -/
-- Proof sketch: apply mathlib's `convexOn_iff_convex_epigraph` to the owner finite real part
-- `withTopRealPart f` on the owner effective domain `dom f`, then rewrite the resulting ordinary
-- epigraph using `WithTopConvexAnalysis.effectiveEpigraph_eq_epigraph_withTopRealPart`.
theorem convexOn_iff_convex_effective_epigraph
    (f : X → WithTop ℝ) :
    ConvexOn ℝ (dom f) (withTopRealPart f) ↔
      Convex ℝ (WithTopConvexAnalysis.effectiveEpigraph f) := by
  simpa [WithTopConvexAnalysis.effectiveEpigraph_eq_epigraph_withTopRealPart] using
    (convexOn_iff_convex_epigraph :
      ConvexOn ℝ (dom f) (withTopRealPart f) ↔
        Convex ℝ {p : X × ℝ | p.1 ∈ dom f ∧ withTopRealPart f p.1 ≤ p.2})
