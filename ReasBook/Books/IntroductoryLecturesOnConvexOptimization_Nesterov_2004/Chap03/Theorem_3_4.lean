/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped WithTopConvexAnalysis

/- Theorem 3.4 lies in the chapter's `WithTop` convex-sublevel-set domain.

Primary domain:
- convex sublevel sets for `WithTop ℝ`-valued functions on an `ℝ`-module.

Relevant owner-style declarations sampled before refinement:
- mathlib `ConvexOn.convex_le`
- mathlib `ConvexOn.convex_lt`
- chapter `withTopRealPart` in `Definition_3_3`
- chapter `constrainedSublevelSet` in `Definition_3_3`

Best owner abstraction:
- core/canonical: `ConvexOn.convex_le`, specialized to
  `ConvexOn ℝ (dom f) (withTopRealPart f)`

Primitive data:
- `dom f`
- `withTopRealPart f`

Derived API:
- `constrainedSublevelSet (dom f) f β`
- the bridge `withTopRealPart_le_iff`
- the source-facing convexity theorem below

Source/core/bridge triage:
- source-facing: `constrainedSublevelSet (dom f) f β`
- core/canonical: `ConvexOn.convex_le`
- bridge/view: `constrainedSublevelSet_dom_eq`, identifying the chapter sublevel-set owner with
  the owner surface `{x ∈ dom f | withTopRealPart f x ≤ β}`

The textbook states the result on `ℝⁿ`, but both the owner theorem and the chapter bridge use
only the ambient `ℝ`-module structure. This file therefore keeps the source-facing `WithTop`
sublevel-set theorem on the public surface and derives it directly from the canonical owner
theorem.
-/

/-- Helper for Theorem 3.4: on the effective domain, the chapter's constrained sublevel set is
exactly the owner sublevel set of the finite real part. -/
theorem constrainedSublevelSet_dom_eq {X : Type u} (f : X → WithTop ℝ) (β : ℝ) :
    constrainedSublevelSet (dom f) f β = {x ∈ dom f | withTopRealPart f x ≤ β} := by
  -- Identify both sets pointwise using the domain membership bridge from Definition 3.3.
  ext x
  constructor
  · rintro ⟨hx, hxβ⟩
    -- Inside the effective domain, the `WithTop` inequality is equivalent to the owner real one.
    exact ⟨hx, (withTopRealPart_le_iff hx).2 hxβ⟩
  · rintro ⟨hx, hxβ⟩
    -- Reversing the same bridge recovers the chapter-facing sublevel-set condition.
    exact ⟨hx, (withTopRealPart_le_iff hx).1 hxβ⟩

namespace ConvexOn

section Convexity

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]
variable {f : X → WithTop ℝ}

/-- Theorem 3.4: if `f` is convex on its effective domain, then each constrained sublevel set of
`f` over that domain is convex. -/
theorem convex_constrainedSublevelSet
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f)) (β : ℝ) :
    Convex ℝ (constrainedSublevelSet (dom f) f β) := by
  -- Rewrite the chapter sublevel set to the owner surface and apply `ConvexOn.convex_le`.
  simpa [constrainedSublevelSet_dom_eq f β] using hf.convex_le β

end Convexity

end ConvexOn
