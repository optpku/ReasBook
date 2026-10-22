/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped MinimalSingularValue

universe u v w

variable {𝕜 : Type w} {E₁ : Type u} {E₂ : Type v}
  [NormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-
Proposition 4.4.1 lies in the normed-space operator / minimal-singular-value domain.

Sampled owner-style declarations:
- `ContinuousLinearMap.minimalSingularValue` with notation `σ_min(A)` in `Definition_4_4_5`, the
  chapter's source-facing owner for the least singular value;
- `minimalSingularValue_def`, the infimum-over-nonzero-vectors bridge for that owner;
- `minimalSingularValue_nonneg`, the canonical positivity API derived from the owner;
- mathlib `ContinuousLinearMap.opNorm` with `ratio_le_opNorm`, the ambient comparison pattern for
  quotient norms of continuous linear maps.

Best owner abstraction:
- source-facing/core: `σ_min(A)` as the chapter owner for the least singular value of a continuous
  linear map;
- bridge/view: `minimalSingularValue_def`, which realizes that owner as the infimum of
  `‖A x‖ / ‖x‖` over nonzero vectors.

Primitive data:
- a continuous linear map `A : E₁ →L[𝕜] E₂`;
- a vector `x : E₁`.

Derived API:
- the pointwise lower bound `σ_min(A) * ‖x‖ ≤ ‖A x‖`.

Source/core/bridge triage:
- source-facing: the textbook lower bound for the image norm in terms of the least singular value;
- core/canonical: the owner `σ_min(A)`;
- bridge/view: evaluate the infimum formula at a fixed nonzero vector.

No extra wrapper is needed here: this proposition is the direct derived inequality attached to the
existing chapter owner. -/

-- Proof sketch: for `x ≠ 0`, the defining infimum of `σ_min(A)` contains the ratio
-- `‖A x‖ / ‖x‖`, so `σ_min(A) ≤ ‖A x‖ / ‖x‖`. Multiplying by `‖x‖` gives the claim.
namespace ContinuousLinearMap

/-- Proposition 4.4.1: the minimal singular value of a continuous linear map gives the lower bound
`σ_min(A) * ‖x‖ ≤ ‖A x‖` for every vector `x`, equivalently `‖A x‖ ≥ σ_min(A) * ‖x‖`. -/
theorem minimalSingularValue_mul_norm_le
    (A : E₁ →L[𝕜] E₂) (x : E₁) :
    σ_min(A) * ‖x‖ ≤ ‖A x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hσx : σ_min(A) ≤ ‖A x‖ / ‖x‖ := by
      rw [minimalSingularValue_def]
      refine csInf_le ?_ ?_
      · refine ⟨0, ?_⟩
        rintro y ⟨v, rfl⟩
        exact div_nonneg (norm_nonneg _) (norm_nonneg _)
      · exact ⟨⟨x, hx⟩, rfl⟩
    exact (le_div_iff₀ hxnorm).1 hσx

end ContinuousLinearMap
