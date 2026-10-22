/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped LevelSetNotation

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Lemma 4.1.9 lies in the nonlinear change-of-variables / convex sublevel-set domain.

Sampled owner declarations:
* project `𝓛[f](a)` / `mem_levelSet_iff` in `Chap01/Definition_1_4_8`, the chapter owner for
  sublevel sets
* mathlib `Equiv.symm_apply_apply` and `Equiv.apply_symm_apply`
* mathlib `ConvexOn.convex_le`
* mathlib `Convex.norm_image_sub_le_of_norm_fderivWithin_le`
* the core canonical sublevel-set expression `(f ⁻¹' Set.Iic a : Set E)`

Source/core/bridge triage:
* source-facing: the distortion estimate on a transformed sublevel set
* core/canonical: an invertible map `u : E ≃ E`, a convex function `φ`, the transformed objective
  `φ ∘ u`, and the chapter owner surface `𝓛[φ](φ (u x0))` and `𝓛[φ ∘ u]((φ ∘ u) x0)`
* bridge/view: the raw preimage forms `φ ⁻¹' Set.Iic (φ (u x0))` and
  `(φ ∘ u) ⁻¹' Set.Iic ((φ ∘ u) x0)`, together with the textbook set-builder forms
  `{z | φ z ≤ φ (u x0)}` and
  `{x | φ (u x) ≤ φ (u x0)}`

Best owner abstraction:
* the previous local structure `NonlinearConvexTransformationCore` was a duplicate wheel
* the mathematically primitive owner layer for this lemma is `u : E ≃ E`, not a bespoke wrapper
* the stronger chapter structure `NonlinearConvexTransformation` packages extra data for later
  results, so using it as the main parameter here would over-strengthen the source lemma

Primitive data:
* `u : E ≃ E`, `φ : E → ℝ`, and `x0 : E`
* whole-space convexity `ConvexOn ℝ Set.univ φ`
* differentiability of `u.symm` on the image-side level set `𝓛[φ](φ (u x0))`
* the derivative-within-set bound
  `‖fderivWithin ℝ u.symm (𝓛[φ](φ (u x0))) z‖ ≤ σ`
  on that same image-side level set

Derived API:
* the x-side transformed level set is `𝓛[φ ∘ u]((φ ∘ u) x0)`
* membership in that level set is exactly the textbook inequality `φ (u x) ≤ φ (u x0)`

The refinement therefore deletes the wrapper structure and its local duplicate objective/sublevel
definitions, keeps the primitive equivalence-level source semantics, and states the item on the
chapter owner layer `𝓛[·](·)` rather than on the raw preimage bridge. -/

section

variable (u : E ≃ E) (φ : E → ℝ) (x0 : E)

local notation "S" => (𝓛[φ]((φ (u x0))) : Set E)
local notation "T" => (𝓛[(φ ∘ u)](((φ ∘ u) x0)) : Set E)

-- Proof sketch: write `x = u.symm (u x)` and `y = u.symm (u y)` using the inverse identities. The
-- image points `u x` and `u y` lie in the convex level set `𝓛[φ](φ (u x0))`, so the whole segment
-- between them stays in that set. Apply the convex mean-value inequality to `u.symm` within this
-- image-side sublevel set and use the uniform within-set derivative bound there.
/-- Lemma 4.1.9: if `φ ∘ u` is obtained from a nonlinear change of variables with convex `φ`, and
`‖fderivWithin ℝ u.symm (𝓛[φ](φ (u x0))) z‖ ≤ σ` on the image-side level set
`𝓛[φ](φ (u x0))`, then any two points of the transformed level set
`𝓛[φ ∘ u]((φ ∘ u) x0)` satisfy
`‖x - y‖ ≤ σ ‖u x - u y‖`. -/
theorem norm_sub_le_sigma_mul_norm_image_sub
    (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hdiff : DifferentiableOn ℝ u.symm S)
    (σ : ℝ)
    (hσ :
      ∀ ⦃z : E⦄, z ∈ S → ‖fderivWithin ℝ u.symm S z‖ ≤ σ)
    {x y : E}
    (hx : x ∈ T)
    (hy : y ∈ T) :
    ‖x - y‖ ≤ σ * ‖u x - u y‖ := by
  have hs : Convex ℝ S := by
    change Convex ℝ (𝓛[φ]((φ (u x0))) : Set E)
    simpa [Function.comp, Set.preimage, Set.mem_Iic, Set.sep_univ] using
      hφ_convex.convex_le ((φ ∘ u) x0)
  have hxS : u x ∈ S := by
    change φ (u x) ≤ (φ ∘ u) x0
    simpa [Function.comp] using hx
  have hyS : u y ∈ S := by
    change φ (u y) ≤ (φ ∘ u) x0
    simpa [Function.comp] using hy
  simpa using hs.norm_image_sub_le_of_norm_fderivWithin_le hdiff hσ hyS hxS

end
