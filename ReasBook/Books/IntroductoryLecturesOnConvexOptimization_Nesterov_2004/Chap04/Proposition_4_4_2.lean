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

universe u v w

variable {𝕜 : Type w} {E₁ : Type u} {E₂ : Type v}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-
Proposition 4.4.2 stays in the normed-space operator / minimal-singular-value domain.

Sampled owner-style declarations:
- `ContinuousLinearMap.minimalSingularValue` with notation `σ_min(A)` in `Definition_4_4_5`, the
  chapter owner for the least singular value;
- `ContinuousLinearMap.minimalSingularValue_mul_norm_le` in `Proposition_4_4_1`, the owner-derived
  lower-bound theorem attached to `σ_min(A)`;
- mathlib `ContinuousLinearMap.bound_of_antilipschitz`, the canonical inverse-map estimate for a
  continuous linear equivalence;
- mathlib `ContinuousLinearMap.opNorm_le_bound`, the owner for upgrading pointwise estimates to an
  operator-norm bound.

Best owner abstraction:
- source-facing/core: the chapter owner `σ_min(A)`;
- bridge/view: inverse/operator-norm estimates for the continuous linear equivalence `A`.

Primitive data:
- an invertible continuous linear operator `A : E₁ ≃L[𝕜] E₂`.

Derived API:
- the reciprocal formula `σ_min(A) = 1 / ‖A⁻¹‖`.

Source/core/bridge triage:
- source-facing: the textbook reciprocal formula for the least singular value of an invertible
  operator;
- core/canonical: the owner `σ_min(A)`;
- bridge/view: Proposition 4.4.1 and the inverse-map operator-norm estimates from mathlib.

No new owner is needed here: this proposition is the inverse-norm companion of the existing owner
`σ_min(A)`. -/

-- Proof sketch: the lower bound `1 / ‖A.symm‖ ≤ σ_min(A)` comes from the canonical
-- `A.antilipschitz` estimate `‖x‖ ≤ ‖A.symm‖ * ‖A x‖`, so every nonzero vector contributes a
-- ratio `‖A x‖ / ‖x‖` bounded below by `1 / ‖A.symm‖`. For the reverse inequality,
-- Proposition 4.4.1 applied to `A` and `A.symm y` gives
-- `‖A.symm y‖ ≤ (1 / σ_min(A)) * ‖y‖`; taking the operator norm of `A.symm` yields
-- `‖A.symm‖ ≤ 1 / σ_min(A)`, hence `σ_min(A) ≤ 1 / ‖A.symm‖`.
namespace ContinuousLinearEquiv

/-- Proposition 4.4.2: for an invertible continuous linear operator, the minimal singular value
equals the reciprocal operator norm of the inverse. -/
theorem minimalSingularValue_eq_inv_norm_symm
    (A : E₁ ≃L[𝕜] E₂) :
    σ_min(A) = 1 / ‖A.symm‖ := by
  by_cases hE : Subsingleton E₁
  · letI := hE
    letI : Subsingleton E₂ := Function.Surjective.subsingleton A.surjective
    rw [show σ_min(A) = 0 by simpa using minimalSingularValue_eq_zero (A : E₁ →L[𝕜] E₂)]
    have hsymm_zero : (A.symm : E₂ →L[𝕜] E₁) = 0 := by
      ext y
      exact Subsingleton.elim _ _
    have hnorm : ‖A.symm‖ = 0 := by
      change ‖(A.symm : E₂ →L[𝕜] E₁)‖ = 0
      simp [hsymm_zero]
    simp [hnorm]
  · letI : Nontrivial E₁ := not_subsingleton_iff_nontrivial.mp hE
    let B : E₂ →L[𝕜] E₁ := A.symm
    have hB_ne : B ≠ 0 := by
      intro hB
      obtain ⟨x, hx⟩ := exists_ne (0 : E₁)
      apply hx
      calc
        x = B (A x) := by simp [B]
        _ = 0 := by simp [B, hB]
    have hB_pos : 0 < ‖B‖ := norm_pos_iff.mpr hB_ne
    have hlower_map : 1 / ‖B‖ ≤ σ_min(A) := by
      change 1 / ‖B‖ ≤ σ_min((A : E₁ →L[𝕜] E₂))
      rw [minimalSingularValue_def]
      refine le_csInf ?_ ?_
      · obtain ⟨x, hx⟩ := exists_ne (0 : E₁)
        exact ⟨_, ⟨⟨x, hx⟩, rfl⟩⟩
      · intro b hb
        rcases hb with ⟨x, rfl⟩
        have hxbound : ‖x.1‖ ≤ ‖B‖ * ‖A x.1‖ := by
          simpa [B] using
            (A : E₁ →L[𝕜] E₂).bound_of_antilipschitz A.antilipschitz x.1
        have hxnorm : 0 < ‖x.1‖ := norm_pos_iff.mpr x.2
        have hdiv : ‖x.1‖ / ‖B‖ ≤ ‖A x.1‖ := by
          exact (div_le_iff₀ hB_pos).2 (by simpa [mul_comm] using hxbound)
        have hmul : (1 / ‖B‖) * ‖x.1‖ ≤ ‖A x.1‖ := by
          simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using hdiv
        exact (le_div_iff₀ hxnorm).2 hmul
    have hlower : 1 / ‖B‖ ≤ σ_min(A) := by
      simpa using hlower_map
    have hσ_pos : 0 < σ_min(A) :=
      lt_of_lt_of_le (one_div_pos.mpr hB_pos) hlower
    have hnorm_bound : ‖B‖ ≤ 1 / σ_min(A) := by
      refine B.opNorm_le_bound (by positivity) fun y ↦ ?_
      have hy : σ_min(A) * ‖B y‖ ≤ ‖y‖ := by
        simpa [B] using
          (A : E₁ →L[𝕜] E₂).minimalSingularValue_mul_norm_le (A.symm y)
      have hdiv : ‖B y‖ ≤ ‖y‖ / σ_min(A) := by
        exact (le_div_iff₀ hσ_pos).2 (by simpa [mul_comm] using hy)
      simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
    simpa [B] using le_antisymm ((le_one_div hB_pos hσ_pos).1 hnorm_bound) hlower

end ContinuousLinearEquiv
