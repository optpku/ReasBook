/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

/- Proposition 1.5.6 is `source-facing` in first-order smooth optimization.

Source/core/bridge triage:
* source-facing: the textbook affine objective `x ↦ α + ⟪a, x⟫` belongs to `C^{1,1}_0`
* core/canonical: the primitive affine owner `E →ᴬ[ℝ] ℝ` together with the Chapter 1 target
  predicate `ContDiff ℝ 1 f ∧ LipschitzWith 0 (∇ f)` from Definition 1.5.2
* bridge/view: coercion from `ContinuousAffineMap` to functions, and the owner-side gradient
  formula below

Primary domain:
* affine real-valued objectives on real Hilbert spaces

Sampled owner-style declarations:
* `ContinuousAffineMap.contDiff`
* `ContinuousAffineMap.hasFDerivAt`
* `ContDiff ℝ 1 f`
* `LipschitzWith L (∇ f)`
* `LipschitzWith.const`

Best owner abstraction:
* `ContinuousAffineMap ℝ E ℝ` for the affine objective itself

Primitive data:
* a continuous affine functional `f : E →ᴬ[ℝ] ℝ`

Derived API:
* its `C¹` regularity
* the constant-gradient formula
* the global `0`-Lipschitz bound on the gradient

The proposition stays source-facing, but its proof now factors through the canonical affine owner
instead of rebuilding the affine calculus directly on the raw lambda term.

The textbook statement is about `ℝⁿ`, but the proof only uses the real Hilbert-space gradient API,
so the canonical owner theorem lives at that intrinsic level.
-/

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace ContinuousAffineMap

/-- The gradient of a real-valued continuous affine functional is the constant field given by its
linear part under the Riesz identification. -/
theorem gradient_eq (f : E →ᴬ[ℝ] ℝ) :
    ∇ (f : E → ℝ) = fun _ : E ↦ (InnerProductSpace.toDual ℝ E).symm f.contLinear :=
  _root_.gradient_eq fun _ ↦ f.hasFDerivAt.hasGradientAt

/-- A real-valued continuous affine functional is `C¹` and has globally `0`-Lipschitz gradient. -/
theorem contDiff_one_and_gradient_lipschitz_zero (f : E →ᴬ[ℝ] ℝ) :
    ContDiff ℝ 1 (f : E → ℝ) ∧ LipschitzWith 0 (∇ (f : E → ℝ)) := by
  refine ⟨by simpa using f.contDiff, ?_⟩
  rw [f.gradient_eq]
  exact LipschitzWith.const ((InnerProductSpace.toDual ℝ E).symm f.contLinear)

end ContinuousAffineMap

/-- Proposition 1.5.6: the affine function `x ↦ α + ⟪a, x⟫` is `C¹` and its gradient is globally
`0`-Lipschitz, equivalently it belongs to the class `C^{1,1}_0`. This is the intrinsic
Hilbert-space form of the textbook `ℝⁿ` statement. -/
-- Proof sketch: package `x ↦ α + ⟪a, x⟫` as the continuous affine functional
-- `(innerSL ℝ a).toContinuousAffineMap +ᵥ ContinuousAffineMap.const ℝ E α`, apply the owner-level
-- `ContinuousAffineMap.contDiff_one_and_gradient_lipschitz_zero`, and then evaluate the coercion.
theorem affineFunction_contDiff_and_gradient_lipschitz_zero
    (α : ℝ) (a : E) :
    ContDiff ℝ 1 (fun x : E ↦ α + inner ℝ a x) ∧
      LipschitzWith 0 (∇ (fun x : E ↦ α + inner ℝ a x)) := by
  let f : E →ᴬ[ℝ] ℝ :=
    (innerSL ℝ a).toContinuousAffineMap +ᵥ ContinuousAffineMap.const ℝ E α
  have hf : (f : E → ℝ) = fun x : E ↦ α + inner ℝ a x := by
    funext x
    simp [f, add_comm]
  simpa [hf] using f.contDiff_one_and_gradient_lipschitz_zero

end
