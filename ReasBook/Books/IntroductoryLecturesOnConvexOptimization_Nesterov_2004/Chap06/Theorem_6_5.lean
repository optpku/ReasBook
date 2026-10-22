/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_35

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

-- Proof sketch: rewrite `τ k` as
-- `(α (k - 1) - α (k + 1)) / α (k - 1)`, square to obtain the left-hand side as
-- `(α (k + 1) - α (k - 1)) ^ 2 / (α (k - 1)) ^ 2`, substitute
-- `λ₁ k * λ₂ k = α k * α (k - 1)`, and clear the positive denominator `(α (k - 1)) ^ 2`.
/-- Theorem 6.5: for a fixed index `k`, if
`α_{k-1} ≠ 0`, `λ₁,k λ₂,k = α_k α_{k-1}`, and
`τ_k = 1 - α_{k+1} / α_{k-1}`, then the step-size inequality
`τ_k^2 ≤ (α_{k+1} / α_{k-1}) λ₁,k λ₂,k` is equivalent to the three-term inequality
`(α_{k+1} - α_{k-1})^2 ≤ α_{k+1} α_k α_{k-1}^2`. -/
theorem tau_square_bound_iff_alpha_three_term_inequality
    (α : Set.Ici (-1 : ℤ) → 𝕜) (lambda₁ lambda₂ τ : ℕ → 𝕜) (k : ℕ)
    (hα_pred_ne : α (switching_parameters_pred_index k) ≠ 0)
    (hprod : lambda₁ k * lambda₂ k =
      α (switching_parameters_curr_index k) * α (switching_parameters_pred_index k))
    (hτ : τ k = 1 - α (switching_parameters_succ_index k) / α (switching_parameters_pred_index k)) :
    τ k ^ (2 : ℕ) ≤
        (α (switching_parameters_succ_index k) / α (switching_parameters_pred_index k)) *
          (lambda₁ k * lambda₂ k) ↔
      (α (switching_parameters_succ_index k) - α (switching_parameters_pred_index k)) ^ (2 : ℕ) ≤
        α (switching_parameters_succ_index k) * α (switching_parameters_curr_index k) *
          (α (switching_parameters_pred_index k)) ^ (2 : ℕ) := by
  let aPred : 𝕜 := α (switching_parameters_pred_index k)
  let aCurr : 𝕜 := α (switching_parameters_curr_index k)
  let aSucc : 𝕜 := α (switching_parameters_succ_index k)
  have haPred_ne : aPred ≠ 0 := by
    simpa [aPred] using hα_pred_ne
  change τ k ^ (2 : ℕ) ≤ (aSucc / aPred) * (lambda₁ k * lambda₂ k) ↔
      (aSucc - aPred) ^ (2 : ℕ) ≤ aSucc * aCurr * aPred ^ (2 : ℕ)
  have hτ_sq :
      τ k ^ (2 : ℕ) = (aSucc - aPred) ^ (2 : ℕ) / aPred ^ (2 : ℕ) := by
    rw [hτ]
    simp only [aPred, aSucc]
    field_simp [haPred_ne]
    ring
  have hprod' : lambda₁ k * lambda₂ k = aCurr * aPred := by
    simpa [aCurr, aPred] using hprod
  rw [hτ_sq, hprod']
  have haPred_sq_pos : 0 < aPred ^ (2 : ℕ) := by
    simpa using sq_pos_of_ne_zero haPred_ne
  rw [div_le_iff₀ haPred_sq_pos]
  field_simp [haPred_ne]

end
