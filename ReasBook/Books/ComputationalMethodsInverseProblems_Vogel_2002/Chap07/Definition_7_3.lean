/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_1

public section

noncomputable section

universe u v w

section DiscrepancyParameter

variable {n : Type u} [Fintype n]
variable {τ : Type w}

/-- Definition 7.3-extra-1. A parameter satisfies the discrete discrepancy
principle when the normalized squared residual energy equals `σ ^ 2`. -/
def IsDiscrepancyParameter (rfamily : τ → EuclideanSpace ℝ n) (σ : ℝ) (a : τ) :
    Prop :=
  predictiveRisk (rfamily a) = σ ^ 2

/-- The defining characterization of `IsDiscrepancyParameter`. -/
@[simp] theorem IsDiscrepancyParameter_iff (rfamily : τ → EuclideanSpace ℝ n) (σ : ℝ)
    (a : τ) :
    IsDiscrepancyParameter rfamily σ a ↔ predictiveRisk (rfamily a) = σ ^ 2 := Iff.rfl

end DiscrepancyParameter

section DiscrepancyBridges

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {τ : Type w}

/-- Rewriting `IsDiscrepancyParameter` for a family of regularized residuals. -/
theorem IsDiscrepancyParameter_iff_regularizedResidual
    (Afamily : τ → Matrix n n ℝ) (σ : ℝ) (d : EuclideanSpace ℝ n) (a : τ) :
    IsDiscrepancyParameter (fun a ↦ regularizedResidual (Afamily a) d) σ a ↔
      ‖regularizedResidual (Afamily a) d‖ ^ 2 / (Fintype.card n : ℝ) = σ ^ 2 := by
  rw [IsDiscrepancyParameter_iff, predictiveRisk_def]

variable {m : Type v} [Fintype m] [DecidableEq m]

/-- Rewriting `IsDiscrepancyParameter` through the explicit residual
`K.toEuclideanLin (regularizedSolution (Rfamily a) d) - d`. -/
theorem IsDiscrepancyParameter_influenceMatrix_iff
    (K : Matrix n m ℝ) (Rfamily : τ → Matrix m n ℝ) (σ : ℝ)
    (d : EuclideanSpace ℝ n) (a : τ) :
    IsDiscrepancyParameter
        (fun a ↦ regularizedResidual (influenceMatrix K (Rfamily a)) d) σ a ↔
      ‖K.toEuclideanLin (regularizedSolution (Rfamily a) d) - d‖ ^ 2 /
          (Fintype.card n : ℝ) = σ ^ 2 := by
  rw [IsDiscrepancyParameter_iff_regularizedResidual,
    regularizedResidual_influenceMatrix]

end DiscrepancyBridges

end
