/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_36

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

-- Proof sketch: rewrite `1 - τ k` as `α ((k : ℤ) + 1) / α ((k : ℤ) - 1)` and clear this
-- positive denominator to reduce to Theorem 6.5.
/-- Corollary 6.2.1: for a fixed index `k`, if
`λ₁,k λ₂,k = α_k α_{k-1}` and `τ_k = 1 - α_{k+1} / α_{k-1}` with
`α_{k-1}, α_{k+1} > 0`, then the step-size condition
`τ_k^2 / (1 - τ_k) ≤ λ_{1,k} λ_{2,k}` is equivalent to
`(α_{k+1} - α_{k-1})^2 ≤ α_{k+1} α_k α_{k-1}^2`. -/
theorem step_size_condition_iff_alpha_three_term_inequality
    (α : Set.Ici (-1 : ℤ) → 𝕜) (lambda₁ lambda₂ τ : ℕ → 𝕜) (k : ℕ)
    (hα_pred_pos : 0 < α (switching_parameters_pred_index k))
    (hα_succ_pos : 0 < α (switching_parameters_succ_index k))
    (hprod : lambda₁ k * lambda₂ k =
      α (switching_parameters_curr_index k) * α (switching_parameters_pred_index k))
    (hτ : τ k = 1 - α (switching_parameters_succ_index k) / α (switching_parameters_pred_index k)) :
    τ k ^ (2 : ℕ) / (1 - τ k) ≤ lambda₁ k * lambda₂ k ↔
      (α (switching_parameters_succ_index k) - α (switching_parameters_pred_index k)) ^ (2 : ℕ) ≤
        α (switching_parameters_succ_index k) * α (switching_parameters_curr_index k) *
          (α (switching_parameters_pred_index k)) ^ (2 : ℕ) := by
  let aPred : 𝕜 := α (switching_parameters_pred_index k)
  let aCurr : 𝕜 := α (switching_parameters_curr_index k)
  let aSucc : 𝕜 := α (switching_parameters_succ_index k)
  have haPred_ne : aPred ≠ 0 := ne_of_gt <| by
    simpa [aPred] using hα_pred_pos
  have haRatio_pos : 0 < aSucc / aPred := by
    -- The source route uses positivity of the adjacent `α` terms to control the denominator.
    refine div_pos ?_ ?_
    · simpa [aSucc] using hα_succ_pos
    · simpa [aPred] using hα_pred_pos
  have hone_sub_tau : 1 - τ k = aSucc / aPred := by
    -- Rewriting `1 - τ k` into the `α`-ratio is the bridge to Theorem 6.5.
    rw [hτ]
    ring
  have hstep :
      τ k ^ (2 : ℕ) / (1 - τ k) ≤ lambda₁ k * lambda₂ k ↔
        τ k ^ (2 : ℕ) ≤ (aSucc / aPred) * (lambda₁ k * lambda₂ k) := by
    -- Clearing the positive denominator matches the left-hand side of Theorem 6.5.
    rw [hone_sub_tau]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (div_le_iff₀ haRatio_pos :
        τ k ^ (2 : ℕ) / (aSucc / aPred) ≤ lambda₁ k * lambda₂ k ↔
          τ k ^ (2 : ℕ) ≤ lambda₁ k * lambda₂ k * (aSucc / aPred))
  have haPred_sq_pos : 0 < aPred ^ (2 : ℕ) := by
    -- Squaring preserves positivity, so the later denominator clearing is valid.
    simpa using sq_pos_of_ne_zero haPred_ne
  have hmain :
      τ k ^ (2 : ℕ) ≤ (aSucc / aPred) * (lambda₁ k * lambda₂ k) ↔
        (aSucc - aPred) ^ (2 : ℕ) ≤ aSucc * aCurr * aPred ^ (2 : ℕ) := by
    have hτ_sq :
        τ k ^ (2 : ℕ) = (aSucc - aPred) ^ (2 : ℕ) / aPred ^ (2 : ℕ) := by
      -- Expanding `τ k` turns the left-hand side into a square over `aPred ^ 2`.
      rw [hτ]
      simp only [aPred, aSucc]
      field_simp [haPred_ne]
      ring
    have hprod' : lambda₁ k * lambda₂ k = aCurr * aPred := by
      -- Re-express the product hypothesis in the local alias notation.
      simpa [aCurr, aPred] using hprod
    -- Once both hypotheses are normalized, the remaining step is a single denominator clear.
    rw [hτ_sq, hprod']
    rw [div_le_iff₀ haPred_sq_pos]
    field_simp [haPred_ne]
  -- After the denominator rewrite, the normalized square inequality finishes the corollary.
  simpa [aPred, aCurr, aSucc] using hstep.trans hmain

end
