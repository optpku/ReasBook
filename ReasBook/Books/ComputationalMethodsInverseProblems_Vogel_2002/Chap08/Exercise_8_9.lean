/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_4.Clauses

public section

open scoped Matrix

namespace TVPrimalDualNewton

/- Exercise 8.9 (1). The displayed formula `(8.61)` for `L̄` is already the
iterate-wise extractor theorem
`TVPrimalDualNewton.HasIntermediateAssignments.lbar_eq`. -/
#check TVPrimalDualNewton.HasIntermediateAssignments.lbar_eq

/-- Exercise 8.9 (2). The reduced system `(8.62)` follows from the inverse-form
Newton step once `Kᵀ * K + α • lbar n` is invertible. -/
theorem HasNewtonAndDualIncrements.reducedSystem_eq
    {ι δ κ : Type} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    {K : Matrix κ ι ℝ} {Dx Dy : Matrix δ ι ℝ} {α : ℝ}
    {f : ℕ → ι → ℝ} {uDual : ℕ → δ → ℝ}
    {bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ}
    {lbar : ℕ → Matrix ι ι ℝ} {r deltaF : ℕ → ι → ℝ}
    {deltaU deltaV : ℕ → δ → ℝ}
    (h : HasNewtonAndDualIncrements
      K Dx Dy α f uDual bInv E11 E12 E21 E22 lbar r deltaF deltaU deltaV)
    (n : ℕ) [Invertible (Kᵀ * K + α • lbar n)] :
    Matrix.mulVec (Kᵀ * K + α • lbar n) (deltaF n) = r n := by
  rw [h.deltaF_eq n, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

end TVPrimalDualNewton
