/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped MinimalSingularValue

universe u₀ u₁ u₂ u₃

/-
Proposition 4.4.3 lies in the chapter's continuous-linear-operator / minimal-singular-value
domain.

Sampled owner-style declarations:
- `minimalSingularValue` and `minimalSingularValue_def` in `Definition_4_4_5`, the source-facing
  owner for `σ_min`
- `minimalSingularValue_eq_zero` in `Definition_4_4_5`, the owner-level degenerate-domain API
- `ContinuousLinearMap.minimalSingularValue_mul_norm_le` in `Proposition_4_4_1`, the canonical
  lower-bound API derived from that owner
- mathlib `ContinuousLinearMap.opNorm_comp_le`, the ambient operator-composition comparison pattern

Best owner abstraction:
- source-facing/core: `minimalSingularValue` with its derived lower-bound theorem
  `ContinuousLinearMap.minimalSingularValue_mul_norm_le`

Primitive data:
- continuous linear maps `A₁ : E₁ →L[𝕜] E₂` and `A₂ : E₀ →L[𝕜] E₁`

Derived API:
- the supermultiplicative lower bound for `σ_min(A₁.comp A₂)`

Source/core/bridge triage:
- source-facing: the textbook supermultiplicativity statement for the minimal singular value
- core/canonical: `minimalSingularValue` and
  `ContinuousLinearMap.minimalSingularValue_mul_norm_le`
- bridge/view: `minimalSingularValue_eq_zero` for the degenerate-domain boundary case

This file therefore reuses the chapter owner theorem from Proposition 4.4.1 directly, in the same
normed-space `σ_min` regime as Definition 4.4.5. -/

variable {𝕜 : Type u₃} {E₀ : Type u₀} {E₁ : Type u₁} {E₂ : Type u₂}
  [NormedField 𝕜]
  [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

-- Proof sketch: apply Proposition 4.4.1 first to `A₂ x`, obtaining
-- `‖A₁ (A₂ x)‖ ≥ σ_min(A₁) * ‖A₂ x‖`, and then again to `A₂` to bound
-- `‖A₂ x‖` from below by `σ_min(A₂) * ‖x‖`. Dividing by `‖x‖` for each nonzero `x` gives the
-- lower bound for `σ_min(A₁.comp A₂)`.
namespace ContinuousLinearMap

/-- Proposition 4.4.3: the minimal singular value is supermultiplicative under composition,
so `σ_min(A₁.comp A₂)` is at least `σ_min(A₁) * σ_min(A₂)`. -/
theorem minimalSingularValue_comp_ge_mul
    (A₁ : E₁ →L[𝕜] E₂) (A₂ : E₀ →L[𝕜] E₁) :
    σ_min(A₁.comp A₂) ≥ σ_min(A₁) * σ_min(A₂) := by
  by_cases hE₀ : Subsingleton E₀
  · letI := hE₀
    rw [minimalSingularValue_eq_zero (A₁.comp A₂), minimalSingularValue_eq_zero A₂]
    simp
  · letI : Nontrivial E₀ := not_subsingleton_iff_nontrivial.mp hE₀
    rw [minimalSingularValue_def]
    refine le_csInf ?_ ?_
    · obtain ⟨x, hx⟩ := exists_ne (0 : E₀)
      exact Set.range_nonempty_iff_nonempty.mpr ⟨⟨x, hx⟩⟩
    · rintro _ ⟨x, rfl⟩
      have hxnorm : 0 < ‖x.1‖ := norm_pos_iff.mpr x.2
      have hA₂ : σ_min(A₂) * ‖x.1‖ ≤ ‖A₂ x.1‖ := by
        simpa using A₂.minimalSingularValue_mul_norm_le x.1
      have hA₁ : σ_min(A₁) * ‖A₂ x.1‖ ≤ ‖A₁ (A₂ x.1)‖ := by
        simpa using A₁.minimalSingularValue_mul_norm_le (A₂ x.1)
      have hmul : (σ_min(A₁) * σ_min(A₂)) * ‖x.1‖ ≤ ‖A₁ (A₂ x.1)‖ := by
        calc
          (σ_min(A₁) * σ_min(A₂)) * ‖x.1‖ = σ_min(A₁) * (σ_min(A₂) * ‖x.1‖) := by
            ring
          _ ≤ σ_min(A₁) * ‖A₂ x.1‖ := by
            exact mul_le_mul_of_nonneg_left hA₂ (minimalSingularValue_nonneg A₁)
          _ ≤ ‖A₁ (A₂ x.1)‖ := hA₁
      exact (le_div_iff₀ hxnorm).2 <| by
        simpa using hmul

end ContinuousLinearMap
