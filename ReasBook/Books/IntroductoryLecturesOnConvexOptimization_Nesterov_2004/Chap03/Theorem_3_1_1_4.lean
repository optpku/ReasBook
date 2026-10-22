/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.1.1.4 lies in the chapter's closed-convex-function domain.

Primary domain:
- closed convex `WithTop ℝ`-valued functions on real topological modules.

Sampled owner-style declarations:
- `ClosedConvexOn` and `ClosedConvexFunction` in `Definition_3_1_1_5`
- `ClosedConvexOn.isClosed_constrainedEpigraph`
- `ClosedConvexOn.convex_constrainedEpigraph`
- `constrainedEpigraph` in `Definition_3_3`

Best owner abstraction:
- `ClosedConvexFunction f`

Primitive data:
- the effective domain `withTopEffectiveDomain f`
- the closedness and convexity of the constrained epigraph packaged by
  `ClosedConvexFunction f`

Derived API:
- the closedness and convexity of the real sublevel sets `{x | f x ≤ β}`

Source/core/bridge triage:
- source-facing: Theorem 3.1.1.4 itself, the sublevel-set consequence of closed convexity
- core/canonical: `ClosedConvexFunction`
- bridge/view: `constrainedEpigraph`

This item is therefore kept at the owner-theorem layer and reduced to the actual source-facing
sublevel-set statement, without introducing separate set owners or additional minimizer/existence
results under the numbered theorem. -/

universe u

open scoped WithTopConvexAnalysis

section

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/-- Theorem 3.1.1.4: every real sublevel set of a closed convex function is closed and convex. -/
-- Proof sketch: identify `{x | f x ≤ β}` with the horizontal slice of the closed convex epigraph
-- of `f` at height `β`; closedness and convexity are inherited from that slice.
theorem ClosedConvexFunction.isClosed_convex_sublevelSet
    {f : X → WithTop ℝ} (hf : ClosedConvexFunction f) (β : ℝ) :
    IsClosed {x | f x ≤ β} ∧ Convex ℝ {x | f x ≤ β} := by
  have hβ_top : (((β : ℝ) : WithTop ℝ) < ⊤) := by simp
  have hclosed_set :
      {x | f x ≤ β} = (fun x : X ↦ (x, β)) ⁻¹' constrainedEpigraph (dom f) f := by
    ext x
    constructor
    · intro hx
      have hxdom : x ∈ dom f := lt_of_le_of_lt hx hβ_top
      exact ⟨hxdom, hx⟩
    · rintro ⟨_, hx⟩
      exact hx
  have hconvex_set :
      {x | f x ≤ β} = {x ∈ dom f | withTopRealPart f x ≤ β} := by
    ext x
    constructor
    · intro hx
      have hxdom : x ∈ dom f := lt_of_le_of_lt hx hβ_top
      exact ⟨hxdom, (withTopRealPart_le_iff hxdom).2 hx⟩
    · rintro ⟨hxdom, hxβ⟩
      exact (withTopRealPart_le_iff hxdom).1 hxβ
  refine ⟨?_, ?_⟩
  · rw [hclosed_set]
    exact IsClosed.preimage (by continuity) hf.isClosed_constrainedEpigraph
  · rw [hconvex_set]
    exact hf.convexOn_withTopRealPart.convex_le β

end
