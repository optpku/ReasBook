/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/- Theorem 3.1.2.2 belongs to the chapter's closed-convex affine-pullback calculus.

Primary domain:
- closed convex `WithTop ℝ`-valued functions and affine preimages of constrained epigraphs on real
  topological modules.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`
- `ClosedConvexOn.isClosed_constrainedEpigraph`
- `ClosedConvexOn.convex_constrainedEpigraph`
- mathlib `ContinuousAffineMap`
- mathlib `ConvexOn.comp_affineMap`

Best owner abstraction:
- `ClosedConvexOn`

Primitive data:
- the owner witness `hφ : ClosedConvexOn S φ`
- the continuous affine map `g : X →ᴬ[ℝ] Y`

Derived API:
- the owner pullback theorem `ClosedConvexOn.comp_continuousAffineMap`
- the Euclidean specialization `ClosedConvexOn.comp_affineMap`
- the epigraph-preimage bridge used in the proof

Source/core/bridge triage:
- source-facing: the theorem asserting closed convexity of the affine pullback on `g ⁻¹' S`
- core/canonical: `ClosedConvexOn`
- bridge/view: the constrained-epigraph preimage under
  `g.prodMap (ContinuousAffineMap.id ℝ ℝ)`, together with the Euclidean specialization from
  affine maps to continuous affine maps

The public owner theorem therefore lives directly in the `ClosedConvexOn` namespace at the
continuous-affine-map level. The textbook `ℝⁿ` affine-map statement remains as a thin
finite-dimensional specialization, while the epigraph preimage argument stays internal to the
proof rather than becoming a parallel wrapper declaration.
-/

namespace ClosedConvexOn

section ContinuousAffineMap

variable {X Y : Type*}
variable [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
variable [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
variable {S : Set Y} {φ : Y → WithTop ℝ}

/-- Closed convexity is preserved by precomposition with a continuous affine map. This is the
canonical owner-level pullback theorem; Euclidean affine-map statements should be derived from it.
-/
-- Proof sketch: identify the constrained epigraph of the pullback with the preimage of
-- `constrainedEpigraph S φ` under the affine map `(x, t) ↦ (g x, t)`. Closedness follows from
-- continuity of this map, and convexity follows from preservation of convexity under affine
-- preimages.
theorem comp_continuousAffineMap
    (hφ : ClosedConvexOn S φ) (g : X →ᴬ[ℝ] Y) :
    ClosedConvexOn (g ⁻¹' S) (φ ∘ g) := by
  let G : X × ℝ →ᴬ[ℝ] Y × ℝ := g.prodMap (ContinuousAffineMap.id ℝ ℝ)
  have hpreimage :
      constrainedEpigraph (g ⁻¹' S) (φ ∘ g) =
        G ⁻¹' constrainedEpigraph S φ := by
    ext p
    simp [G, constrainedEpigraph]
  refine ⟨fun x hx ↦ hφ.subset_withTopEffectiveDomain hx, ?_, ?_⟩
  · rw [hpreimage]
    exact hφ.isClosed_constrainedEpigraph.preimage G.continuous
  · have hconv : Convex ℝ (G ⁻¹' constrainedEpigraph S φ) := by
      simpa using hφ.convex_constrainedEpigraph.affine_preimage G.toAffineMap
    simpa [hpreimage] using hconv

end ContinuousAffineMap

section AffineMap

/-- Theorem 3.1.2.2: if `φ` is closed and convex on `S ⊆ ℝᵐ` and `g : ℝⁿ → ℝᵐ` is affine, then
the pullback `x ↦ φ (g x)` is closed and convex on the affine preimage `{x | g x ∈ S}`. This is
the finite-dimensional specialization of `ClosedConvexOn.comp_continuousAffineMap`. -/
theorem comp_affineMap
    {m n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin m))}
    {φ : EuclideanSpace ℝ (Fin m) → WithTop ℝ}
    (hφ : ClosedConvexOn S φ)
    (g : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin m)) :
    ClosedConvexOn (g ⁻¹' S) (φ ∘ g) :=
  comp_continuousAffineMap hφ ⟨g, g.continuous_of_finiteDimensional⟩

end AffineMap

end ClosedConvexOn

end
