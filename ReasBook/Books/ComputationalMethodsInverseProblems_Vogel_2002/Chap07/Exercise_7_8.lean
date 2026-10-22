/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_5
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Exercise_7_8.Deblurring

public section

noncomputable section

section

/-- Exercise 7.8. In the discrete image-deblurring setting, the
minimum-bound method chooses `α` exactly by minimizing the Chapter 7
`minimumBound` functional for the Tikhonov residual family of the observed
image. The source text discusses this in the regime `γ > 1`, but the
characterization itself is the canonical specialization of
`IsMinimumBoundParameter_iff`. -/
theorem imageDeblurringMinimumBoundMethod_iff {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (dObs : Matrix (Fin n_x) (Fin n_y) ℝ) (γ σ α : ℝ) :
    IsMinimumBoundParameter (imageDeblurringBlurMatrix psf)
      (imageDeblurringResidualFamily psf dObs) γ σ α ↔
      α ∈ Set.Ioi (0 : ℝ) ∧
        IsMinOn
          (minimumBound (imageDeblurringBlurMatrix psf)
            (imageDeblurringResidualFamily psf dObs) γ σ)
          (Set.Ioi (0 : ℝ)) α := by
  exact
    (IsMinimumBoundParameter_iff
      (imageDeblurringBlurMatrix psf)
      (imageDeblurringResidualFamily psf dObs) γ σ α)

end
