/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped RealInnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Example 2.1.1.1 lies in convex analysis of affine functionals on real inner product spaces.

Sampled owner-style declarations in this domain:
* mathlib `ConvexOn.comp_affineMap`
* mathlib `convexOn_id`
* mathlib `LinearMap.toAffineMap`
* mathlib `innerSL_apply_apply`

Best owner abstraction:
* `ConvexOn.comp_affineMap`, with the affine functional itself carried by `E →ᵃ[ℝ] ℝ`

Primitive data:
* the convex set `s`
* the affine functional `AffineMap.const ℝ E alpha + ((innerSL ℝ a).toLinearMap).toAffineMap`

Derived API:
* the source-facing convexity theorem for `x ↦ alpha + ⟪a, x⟫`, obtained by restricting the
  whole-space affine-owner convexity to `s`

Source/core/bridge triage:
* source-facing: Example 2.1.1.1's affine-inner convexity statement
* core/canonical: `ConvexOn.comp_affineMap`
* bridge/view: the affine functional
  `AffineMap.const ℝ E alpha + ((innerSL ℝ a).toLinearMap).toAffineMap`; the textbook `ℝⁿ` form
  is the Euclidean specialization of this intrinsic theorem

The previous proof decomposed the affine functional into a linear owner plus a constant-shift
lemma. This refinement keeps the same theorem, but treats the affine functional itself as the
owner object and derives convexity from `convexOn_id` via `ConvexOn.comp_affineMap`. -/

/-- Example 2.1.1.1:
Every function of the form `x ↦ α + ⟪a, x⟫` on a real inner product space is convex on a convex
set. The textbook `ℝⁿ` statement is the Euclidean specialization. -/
-- Proof sketch: package `x ↦ alpha + ⟪a, x⟫` as the affine map
-- `AffineMap.const ℝ E alpha + ((innerSL ℝ a).toLinearMap).toAffineMap`. Since `id : ℝ → ℝ` is
-- convex on `Set.univ`, its affine precomposition is convex on `Set.univ`; restricting that owner
-- theorem to `s` gives the result.
theorem convexOn_affine_inner (s : Set E)
    (hs : Convex ℝ s) (alpha : ℝ) (a : E) :
    ConvexOn ℝ s (fun x ↦ alpha + ⟪a, x⟫) := by
  let ℓ : E →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ E alpha + ((innerSL ℝ a).toLinearMap).toAffineMap
  have hℓ : ConvexOn ℝ Set.univ (ℓ : E → ℝ) := by
    simpa [Function.comp, ℓ] using
      (convexOn_id convex_univ).comp_affineMap ℓ
  refine ⟨hs, ?_⟩
  intro x hx y hy t u ht hu htu
  simpa [ℓ, innerSL_apply_apply, add_assoc, add_left_comm, add_comm] using
    hℓ.2 (by simp) (by simp) ht hu htu
