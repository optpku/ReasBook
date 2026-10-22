/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Order.ConditionallyCompleteLattice.Finset

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type v} [AddCommGroup E] [Module 𝕜 E]
variable {β : Type w} [ConditionallyCompleteLinearOrder β] [AddCommGroup β]
  [IsOrderedAddMonoid β] [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β]

/- Proposition 3.1 lies in the convex-analysis domain of finite convex-hull maximum principles on
ordered scalar modules.

Sampled owner-style declarations:
- `ConvexOn.le_sup_of_mem_convexHull`
- `ConvexOn.exists_ge_of_mem_convexHull`
- `Finset.sup'_eq_csSup_image`

Best owner abstraction:
- `ConvexOn.le_sup_of_mem_convexHull`

Primitive data:
- a finite nonempty vertex set `t : Finset E`
- an ordered scalar `𝕜` and ordered codomain `β`
- a convex function `hf : ConvexOn 𝕜 C f`
- the source-faithful inclusion `(t : Set E) ⊆ C`

Derived API:
- the equality between the supremum of `f` on `convexHull 𝕜 (t : Set E)` and the supremum of `f`
  on the vertex set `(t : Set E)`
- the finite-maximum reformulation through `t.sup' ht f`

Source/core/bridge triage:
- source-facing: the simplex maximum principle from the textbook proposition
- core/canonical: `ConvexOn.le_sup_of_mem_convexHull`
- bridge/view: `Finset.sup'_eq_csSup_image`, which identifies the supremum on the finite vertex set
  with the finite maximum

The owner theorem is already organized around a finite vertex set, so this file uses the same
primitive data instead of introducing a parallel family-index API. The source-facing content is the
equality of the convex-hull supremum with the vertex supremum, while the ambient scalar and codomain
now remain at the canonical generality already supported by the owner theorem. -/

/-- Proposition 3.1: if a `β`-valued convex function is defined on a set containing a finite
nonempty vertex set `t`, then its supremum on `convexHull 𝕜 (t : Set E)` equals its supremum on
the vertex set itself. Since `t` is finite and nonempty, this is exactly the finite-maximum
statement behind the textbook real-valued simplex maximum principle; specializing `𝕜 = β = ℝ`
recovers the usual formulation. -/
theorem convexOn_sSup_image_convexHull_eq_sSup_image_vertices
    (t : Finset E) (ht : t.Nonempty) {C : Set E} {f : E → β} (hf : ConvexOn 𝕜 C f)
    (htC : (t : Set E) ⊆ C) :
    sSup (f '' convexHull 𝕜 (t : Set E)) = sSup (f '' (t : Set E)) := by
  have hpointwise_upper :
      ∀ y ∈ f '' convexHull 𝕜 (t : Set E), y ≤ t.sup' ht f := by
    rintro _ ⟨x, hx, rfl⟩
    exact hf.le_sup_of_mem_convexHull htC hx
  have hconv_nonempty : (f '' convexHull 𝕜 (t : Set E)).Nonempty :=
    ((Finset.Nonempty.to_set ht).mono (subset_convexHull 𝕜 (t : Set E))).image f
  have hbounded : BddAbove (f '' convexHull 𝕜 (t : Set E)) := ⟨_, hpointwise_upper⟩
  have hvertex_nonempty : (f '' (t : Set E)).Nonempty := (Finset.Nonempty.to_set ht).image f
  have himage_mono : f '' (t : Set E) ⊆ f '' convexHull 𝕜 (t : Set E) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, subset_convexHull 𝕜 (t : Set E) hx, rfl⟩
  have hupper : sSup (f '' convexHull 𝕜 (t : Set E)) ≤ t.sup' ht f :=
    csSup_le hconv_nonempty hpointwise_upper
  have hlower : t.sup' ht f ≤ sSup (f '' convexHull 𝕜 (t : Set E)) := by
    rw [Finset.sup'_eq_csSup_image t ht f]
    exact csSup_le_csSup hbounded hvertex_nonempty himage_mono
  rw [Finset.sup'_eq_csSup_image t ht f] at hupper hlower
  exact le_antisymm hupper hlower

end
