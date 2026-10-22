/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped ConvexAnalysis

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]

/-
Theorem 3.1.1.2 lives in the chapter's extended-real convex-analysis bridge.

Primary domain:
- convexity of the finite real part of an `EReal`-valued function on its effective domain
- convexity of the corresponding effective epigraph subset of `X × ℝ`

Sampled owner-style declarations before refinement:
- chapter `dom` from `Definition_3_1_1_2`
- chapter `extendedRealRealPart` from `Definition_3_1_1_3`
- chapter `effectiveEpigraph` from `Definition_3_1_1_3`
- mathlib `ConvexOn.convex_epigraph`
- mathlib `convexOn_iff_convex_epigraph`

Best owner abstraction:
- source-facing owner: `effectiveEpigraph f`
- core/canonical: `ConvexOn ℝ (dom f) (extendedRealRealPart f)`
- bridge/view: the definitional identification of `effectiveEpigraph f` with the real epigraph of
  `extendedRealRealPart f` over `dom f`

Primitive data:
- the source-facing owner data `dom f`
- the finite real part `extendedRealRealPart f`
- the effective epigraph owner `effectiveEpigraph f`

Derived API:
- the epigraph-convexity equivalence below

Source/core/bridge triage:
- source-facing: the textbook effective-epigraph convexity criterion on `effectiveEpigraph f`
- core/canonical: mathlib `ConvexOn` and `convexOn_iff_convex_epigraph`
- bridge/view: `dom f`, `extendedRealRealPart f`, and the definitional expansion of
  `effectiveEpigraph f`

The textbook states the result on `ℝⁿ`, but the owner theorem and both imported bridge
constructions use no coordinate, topological, or finite-dimensional structure. The public theorem
therefore lives at the intrinsic real-module level; `ℝⁿ` is a downstream specialization.
-/
/-- Theorem 3.1.1.2: the owner `ConvexOn` formulation for the finite real part of an
extended-real-valued function is equivalent to convexity of its textbook effective epigraph in
`X × ℝ`. -/
-- Proof sketch: apply mathlib's `convexOn_iff_convex_epigraph` to `extendedRealRealPart f` on
-- `dom f`, then unfold the source-facing owner `effectiveEpigraph`.
theorem isConvexExtendedRealFunction_iff_convex_epigraph
    (f : X → EReal) :
    ConvexOn ℝ (dom f) (extendedRealRealPart f) ↔
      Convex ℝ (effectiveEpigraph f) := by
  simpa [effectiveEpigraph] using
    (convexOn_iff_convex_epigraph :
      ConvexOn ℝ (dom f) (extendedRealRealPart f) ↔
        Convex ℝ {p : X × ℝ | p.1 ∈ dom f ∧ extendedRealRealPart f p.1 ≤ p.2})

end
