/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

/- Lemma 3.11 lies in the chapter's extended-valued convex-analysis / affine subdifferential
calculus on Euclidean spaces.

Sampled owner declarations:
- mathlib `ConvexOn.comp_affineMap`
- `ClosedConvexOn.comp_affineMap`
- `IsSubgradientAt.comp_affineMap`
- `subdifferential`
- `mem_subdifferential_iff`

Best owner abstractions:
- `ClosedConvexOn` for the closed-convex affine-pullback statement
- `IsSubgradientAt` and `subdifferential` from `Definition_3_1_5` for the affine subgradient
  calculus statement

Primitive data:
- the affine map `g : Eₙ →ᵃ[ℝ] Eₘ`
- the ambient closed-convex hypothesis `ClosedConvexOn S φ`
- the owner-level subgradient predicate `IsSubgradientAt f (g x) h`

Derived API:
- the recalled owner theorem `ClosedConvexOn.comp_affineMap`
- the Euclidean bridge theorem `subdifferential_comp_affineMap_image_adjoint_subset`

Source/core/bridge triage:
- source-facing: Lemma 3.11's two affine-pullback consequences, namely closed convexity on
  `g ⁻¹' S` and the adjoint-image inclusion for the subdifferential
- core/canonical: `ClosedConvexOn`, `IsSubgradientAt`, and `subdifferential`
- bridge/view: `ConvexOn.comp_affineMap`, which underlies the closed-convex owner theorem, and
  the finite-dimensional set-level subdifferential inclusion derived from
  `IsSubgradientAt.comp_affineMap`

This file therefore recalls the assumption-free closed-convex owner theorem directly and keeps
only the thin affine subdifferential bridge theorem that specializes
`IsSubgradientAt.comp_affineMap` to the
source-facing subdifferential statement. -/

recall ClosedConvexOn.comp_affineMap
    {m n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin m))}
    {φ : EuclideanSpace ℝ (Fin m) → WithTop ℝ}
    (hφ : ClosedConvexOn S φ)
    (g : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin m)) :
    ClosedConvexOn (g ⁻¹' S) (φ ∘ g)

universe u v

/-- Lemma 3.11, subdifferential part: every subgradient of `f` at `g x` pulls back along the
adjoint of the linear part of `g`. In set form, the adjoint image of `∂ f((g x))` is contained in
`∂ (f ∘ g)(x)`. In Euclidean coordinates, when `g y = A y + b`, the pullback is under `Aᵀ`. -/
-- Proof sketch: unpack membership in `subdifferential f (g x)` into the owner predicate
-- `IsSubgradientAt f (g x)`. The owner theorem `IsSubgradientAt.comp_affineMap` pulls that
-- subgradient back along `g.linear.adjoint`, and `mem_subdifferential_iff` repackages the result
-- into the set-valued statement.
theorem subdifferential_comp_affineMap_image_adjoint_subset
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {f : F → WithTop ℝ} {g : E →ᵃ[ℝ] F} {x : E} :
    g.linear.adjoint '' (∂ f((g x))) ⊆ ∂ (f ∘ g)(x) := by
  rintro _ ⟨h, hh, rfl⟩
  simpa [mem_subdifferential_iff] using (mem_subdifferential_iff.mp hh).comp_affineMap

end
