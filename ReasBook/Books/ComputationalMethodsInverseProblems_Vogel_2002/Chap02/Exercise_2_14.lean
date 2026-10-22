/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_19.Reconstruction

public section

noncomputable section

namespace ContinuousLinearMap.SingularSystem

universe u v

variable {H₁ : Type u} {H₂ : Type v}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
variable {K : H₁ →L[ℝ] H₂}

/-- Exercise 2.14. Equation `(2.25)` for the reconstruction operator from `(2.24)` is the
standard operator-norm perturbation estimate specialized to
`S.reconstructionOperator w h_bound`. -/
theorem reconstructionOperator_apply_sub_le
    (S : SingularSystem K) (w : ℝ → ℝ)
    (h_bound : ∃ C ≥ 0, ∀ s > 0, |w (s ^ 2) / s| ≤ C)
    (g₁ g₂ : H₂) :
    ‖S.reconstructionOperator w h_bound g₁ - S.reconstructionOperator w h_bound g₂‖ ≤
      ‖S.reconstructionOperator w h_bound‖ * ‖g₁ - g₂‖ := by
  simpa [ContinuousLinearMap.map_sub] using
    (S.reconstructionOperator w h_bound).le_opNorm (g₁ - g₂)

end ContinuousLinearMap.SingularSystem
