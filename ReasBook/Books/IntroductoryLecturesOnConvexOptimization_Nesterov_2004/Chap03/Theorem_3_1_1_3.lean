/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped ConvexAnalysis

/-
Theorem 3.1.1.3 lies in the chapter's extended-real convex-analysis bridge domain.

Relevant owner-style declarations sampled before refinement:
- mathlib `ConvexOn.convex_le`
- project `mem_levelSet_iff` and `levelSet_eq_setOf` in `Chap01/Definition_1_4_8`, which record
  the chapter’s lower-level-set owner surface
- mathlib `ConvexOn`
- chapter `extendedRealRealPart` in `Definition_3_1_1_3`
- chapter notation `dom f` for `extendedRealEffectiveDomain f`

Best owner abstraction:
- the canonical owner theorem `ConvexOn.convex_le`, specialized to the finite-real-part bridge
  `ConvexOn ℝ (dom f) (extendedRealRealPart f)`

Primitive data:
- `dom f`
- `extendedRealRealPart f`

Derived API:
- the owner sublevel set `{x ∈ dom f | extendedRealRealPart f x ≤ β}`
- the source-facing set-builder `{x ∈ dom f | f x ≤ β}`
- the bridge `extendedRealSublevelSet_dom_eq`, identifying that source-facing sublevel set with
  the owner one
- the convexity statement, which is only direct recall/use of the owner theorem above

Source/core/bridge triage:
- source-facing: the textbook real sublevel-set surface `{x ∈ dom f | f x ≤ β}`
- core/canonical: `ConvexOn.convex_le`
- bridge/view: the identification of the source-facing surface with the owner sublevel set
  `{x ∈ dom f | extendedRealRealPart f x ≤ β}` via `extendedRealRealPart_le_iff`

The textbook states the theorem on `ℝⁿ`, but the bridge object and the owner theorem use only the
ambient `ℝ`-module structure already fixed in `Definition_3_1_1_3`. This file therefore deletes
the duplicate sublevel-set wrapper, records the minimal source-facing bridge theorem, and presents
the numbered item itself as the chapter-specialized owner theorem at `dom f` and
`extendedRealRealPart f`.
-/

/-- On the effective domain, the source-facing `EReal` sublevel set is exactly the owner sublevel
set of the finite real part. -/
theorem extendedRealSublevelSet_dom_eq {X : Type u} (f : X → EReal) (β : ℝ) :
    {x ∈ dom f | f x ≤ β} = {x ∈ dom f | extendedRealRealPart f x ≤ β} := by
  ext x
  constructor
  · rintro ⟨hx, hxβ⟩
    exact ⟨hx, (extendedRealRealPart_le_iff hx).2 hxβ⟩
  · rintro ⟨hx, hxβ⟩
    exact ⟨hx, (extendedRealRealPart_le_iff hx).1 hxβ⟩

section Convexity

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]
variable (f : X → EReal)

/- Theorem 3.1.1.3: if `f` is convex, then each sublevel set
`{x ∈ dom f | extendedRealRealPart f x ≤ β}` is convex. This is exactly the canonical owner
theorem `ConvexOn.convex_le`, specialized to the chapter bridge `extendedRealRealPart`; the
source-facing sublevel set `{x ∈ dom f | f x ≤ β}` is identified with this owner surface by
`extendedRealSublevelSet_dom_eq f`. -/
#check
  (ConvexOn.convex_le :
    ConvexOn ℝ (dom f) (extendedRealRealPart f) →
      ∀ β : ℝ, Convex ℝ {x ∈ dom f | extendedRealRealPart f x ≤ β})

end Convexity

end
