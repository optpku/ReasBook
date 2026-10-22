/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2_2.Discrepancy
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_3
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Exercise_7_8.Deblurring

public section

noncomputable section

section

/-- Exercise 7.5. For the discrete image-deblurring application of Section
7.2.1, `α` satisfies the discrepancy principle exactly when the normalized
squared discrepancy of the blur matrix and observed image vectorization equals
`σ ^ 2`. -/
theorem imageDeblurringDiscrepancyPrinciple_iff {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (dObs : Matrix (Fin n_x) (Fin n_y) ℝ)
    (sigma alpha : ℝ) :
    IsDiscrepancyParameter (imageDeblurringResidualFamily psf dObs) sigma alpha ↔
      Tikhonov.discrepancy (imageDeblurringBlurMatrix psf) (imageAsVector dObs) alpha ^ 2 /
          (Fintype.card (Fin n_x × Fin n_y) : ℝ) = sigma ^ 2 := by
  rw [IsDiscrepancyParameter_iff, predictiveRisk_def, imageDeblurringResidualFamily_eq,
    Tikhonov.discrepancy_eq]

end
