/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace UniformConvexOn

/-- The pointwise maximum of two uniformly convex functions with the same modulus is uniformly
convex. -/
theorem sup
    {Q : Set E} {φ : ℝ → ℝ} {f₁ f₂ : E → ℝ}
    (hf₁ : UniformConvexOn Q φ f₁)
    (hf₂ : UniformConvexOn Q φ f₂) :
    UniformConvexOn Q φ (f₁ ⊔ f₂) := by
  refine ⟨hf₁.1, ?_⟩
  intro x hx y hy a b ha hb hab
  refine sup_le ?_ ?_
  · calc
      f₁ (a • x + b • y) ≤ a • f₁ x + b • f₁ y - a * b * φ ‖x - y‖ := hf₁.2 hx hy ha hb hab
      _ ≤ a • (f₁ x ⊔ f₂ x) + b • (f₁ y ⊔ f₂ y) - a * b * φ ‖x - y‖ := by
          gcongr <;> exact le_sup_left
  · calc
      f₂ (a • x + b • y) ≤ a • f₂ x + b • f₂ y - a * b * φ ‖x - y‖ := hf₂.2 hx hy ha hb hab
      _ ≤ a • (f₁ x ⊔ f₂ x) + b • (f₁ y ⊔ f₂ y) - a * b * φ ‖x - y‖ := by
          gcongr <;> exact le_sup_right

end UniformConvexOn

namespace StrongConvexOn

/- Proposition 3.39 lies in the strong-convexity closure domain.

Sampled owner-style declarations:
- mathlib `UniformConvexOn`
- mathlib `UniformConvexOn.mono`
- mathlib `StrongConvexOn.mono`
- mathlib `ConvexOn.sup`

Best owner abstraction:
- core/canonical closure rule: `UniformConvexOn.sup`
- source-facing specialization: `StrongConvexOn Q μ f`

Primitive data:
- the common feasible set `Q`
- the owner hypotheses `hf₁ : StrongConvexOn Q μ₁ f₁` and `hf₂ : StrongConvexOn Q μ₂ f₂`
- the common weakened modulus `min μ₁ μ₂`

Derived API:
- strong convexity of the pointwise supremum with modulus `min μ₁ μ₂`

Source/core/bridge triage:
- core/canonical: the owner-level equal-modulus closure theorem `UniformConvexOn.sup`
- source-facing: Proposition 3.39 as the quadratic-modulus specialization in the
  `StrongConvexOn` namespace
- bridge/view: weaken both moduli to `min μ₁ μ₂` via `StrongConvexOn.mono` before applying the
  canonical uniform-convexity theorem
-/

/-- Proposition 3.39: the pointwise maximum of two strongly convex functions on the same feasible
set is strongly convex with parameter `min μ₁ μ₂`. -/
-- Proof sketch: first weaken both moduli to `min μ₁ μ₂` using `StrongConvexOn.mono`, then apply
-- the owner-level equal-modulus theorem `UniformConvexOn.sup`.
theorem sup
    {Q : Set E} {f₁ f₂ : E → ℝ} {μ₁ μ₂ : ℝ}
    (hf₁ : StrongConvexOn Q μ₁ f₁)
    (hf₂ : StrongConvexOn Q μ₂ f₂) :
    StrongConvexOn Q (min μ₁ μ₂) (f₁ ⊔ f₂) := by
  have hf₁' : StrongConvexOn Q (min μ₁ μ₂) f₁ := hf₁.mono (min_le_left _ _)
  have hf₂' : StrongConvexOn Q (min μ₁ μ₂) f₂ := hf₂.mono (min_le_right _ _)
  simpa [StrongConvexOn] using UniformConvexOn.sup hf₁' hf₂'

end StrongConvexOn
