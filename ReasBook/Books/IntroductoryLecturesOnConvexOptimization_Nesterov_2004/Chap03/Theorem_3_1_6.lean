/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

namespace ClosedConvexOn

/- Theorem 3.1.6 lies in the chapter's closed-convex affine-pullback calculus.

Primary domain:
- closed convex `WithTop ℝ`-valued functions on Euclidean spaces and affine pullbacks.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`
- `ClosedConvexOn.comp_continuousAffineMap` from `Theorem_3_1_2_2`
- `ClosedConvexOn.comp_affineMap` from `Theorem_3_1_2_2`
- mathlib `ConvexOn.comp_affineMap`

Best owner abstraction:
- `ClosedConvexOn.comp_affineMap`

Primitive data:
- the owner witness `hφ : ClosedConvexOn S φ`
- the linear part `A`
- the translation vector `b`

Derived API:
- the affine map `A.toAffineMap +ᵥ AffineMap.const ℝ Eₙ b`
- the source-facing bridge theorem `ClosedConvexOn.comp_linearMap_add`

Source/core/bridge triage:
- source-facing: the textbook `x ↦ A x + b` specialization
- core/canonical: `ClosedConvexOn.comp_affineMap`
- bridge/view: the affine-map package of `A` and `b`

The boundedness hypothesis from the textbook statement is mathematically redundant for closed
convexity under affine precomposition, so the refined theorem reuses the earlier owner theorem
directly and keeps only the linear-plus-translation source surface.
-/

/-- Theorem 3.1.6: if `φ` is closed and convex on `S ⊆ ℝᵐ`, then the composition
`x ↦ φ (A x + b)` is closed and convex on the inverse image
`{x ∈ ℝⁿ | A x + b ∈ S}`. -/
-- Proof sketch: package `x ↦ A x + b` as an affine map and apply the owner theorem
-- `ClosedConvexOn.comp_affineMap`.
theorem comp_linearMap_add
    {S : Set Eₘ} {φ : Eₘ → WithTop ℝ}
    (hφ : ClosedConvexOn S φ)
    (A : Eₙ →ₗ[ℝ] Eₘ) (b : Eₘ) :
    ClosedConvexOn {x : Eₙ | A x + b ∈ S} (fun x ↦ φ (A x + b)) := by
  simpa using hφ.comp_affineMap (A.toAffineMap +ᵥ AffineMap.const ℝ Eₙ b)

end ClosedConvexOn

end
