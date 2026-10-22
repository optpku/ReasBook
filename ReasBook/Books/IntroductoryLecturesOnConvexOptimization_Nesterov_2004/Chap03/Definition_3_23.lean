/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_22

-- Declarations for this item will be appended below by the statement pipeline.

open ProperCone
open scoped Pointwise Topology
open scoped NormalCone

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Source-facing Lean notation for the textbook tangent-cone family `T_Q`. -/
namespace TangentCone

scoped notation:max "𝒯[" Q "]" => posTangentConeAt Q

end TangentCone

open scoped TangentCone

/- Definition 3.23 belongs to the chapter's canonical tangent-cone API around the owner
abstraction `posTangentConeAt`.

Primary domain:
- tangent and normal cones in real inner-product-space convex analysis.

Relevant declarations sampled before refinement:
- `posTangentConeAt`
- `posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton`
- `normalCone`
- `ProperCone.innerDual_innerDual`

Owner abstraction:
- `posTangentConeAt`

Primitive data:
- the set `Q`
- the base point `xBar`

Derived API:
- the textbook polarization criterion
  `∀ g ∈ N[Q] xBar, 0 ≤ inner ℝ g p`

Source/core/bridge triage:
- source-facing: the textbook tangent-cone criterion at `xBar`
- core/canonical: `posTangentConeAt`
- bridge/view: `mem_tangentCone_iff`

This file therefore recalls the owner declaration directly instead of maintaining a parallel local
`tangentCone` definition. The public bridge theorem now uses the source-facing notation
`𝒯[Q] xBar` for the tangent cone together with Definition 3.22's normal-cone notation `N[Q] xBar`,
so the theorem surface matches the textbook polarity criterion directly. The textbook `ℝⁿ`
statement is a specialization of this owner-level inner-product-space bridge, and the closedness
hypothesis from the prose is omitted because the polarity criterion itself only depends on
convexity and the base-point condition `xBar ∈ Q`. -/

/-- Definition 3.23: for a convex set `Q` in a complete real inner-product space and `xBar ∈ Q`,
membership in the textbook tangent cone `𝒯[Q] xBar` is exactly the polarity condition against
every normal vector `g ∈ N[Q] xBar`. The notation `𝒯[Q] xBar` is the source-facing surface for the
canonical owner `posTangentConeAt Q xBar`, and the textbook `ℝⁿ` statement is the corresponding
specialization. -/
theorem mem_tangentCone_iff {Q : Set E} {xBar p : E}
    (hQ_convex : Convex ℝ Q) (hxBar : xBar ∈ Q) :
    p ∈ 𝒯[Q] xBar ↔
      ∀ g ∈ N[Q] xBar, 0 ≤ inner ℝ g p :=
by
  let S : Set E := Q -ᵥ ({xBar} : Set E)
  have hposTangentConeAt :
      posTangentConeAt Q xBar = closure ((PointedCone.hull ℝ S : Set E)) := by
    simpa [S] using
      posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton Q hQ_convex xBar hxBar
  have hnormal :
      innerDual (closure ((PointedCone.hull ℝ S : Set E))) = N[Q] xBar := by
    ext g
    change g ∈ innerDual (closure ((PointedCone.hull ℝ S : Set E))) ↔ g ∈ innerDual S
    constructor
    · intro hg
      exact fun x hx ↦ hg <| subset_closure <| PointedCone.subset_hull hx
    · intro hg
      rw [mem_innerDual] at hg ⊢
      intro x hx
      let G : ProperCone ℝ E := innerDual ({g} : Set E)
      have hS : S ⊆ (G : Set E) := by
        intro y hy
        simpa [G, mem_innerDual, real_inner_comm] using hg hy
      have hhull : (PointedCone.hull ℝ S : Set E) ⊆ G := Submodule.span_le.mpr hS
      simpa [G, mem_innerDual, real_inner_comm] using
        (G.isClosed.closure_subset_iff.2 hhull) hx
  change p ∈ posTangentConeAt Q xBar ↔ p ∈ innerDual (N[Q] xBar : Set E)
  rw [hposTangentConeAt, ← hnormal]
  let C : ProperCone ℝ E := ⟨(PointedCone.hull ℝ S).closure, isClosed_closure⟩
  change p ∈ C ↔ p ∈ innerDual (((innerDual (C : Set E) : ProperCone ℝ E) : Set E))
  rw [innerDual_innerDual C]
