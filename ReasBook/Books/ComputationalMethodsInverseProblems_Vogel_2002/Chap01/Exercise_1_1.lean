/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_1.Fredholm

public section

noncomputable section

namespace Fredholm1D

/-- Exercise 1.1. Applying midpoint quadrature to the one-dimensional Fredholm operator with
the Gaussian kernel from (1.1)-(1.2) yields the discrete matrix from (1.3), namely
`Fredholm1D.midpointMatrix n C γ`. -/
theorem midpointQuadrature_eq_midpointMatrix
    (n : ℕ) (C γ : ℝ) :
    ((fun i j : Fin n ↦
        let h : ℝ := 1 / n
        let x : Fin n → ℝ := fun a ↦ (((a : ℕ) : ℝ) + (1 / 2 : ℝ)) * h
        h * gaussianKernel C γ (x i - x j)) : Matrix (Fin n) (Fin n) ℝ) =
      midpointMatrix n C γ := by
  ext i j
  simp only [midpointMatrix, gaussianKernel, one_div]
  have hsub :
      ((((i : ℕ) : ℝ) + (2⁻¹ : ℝ)) * (↑n)⁻¹ - ((((j : ℕ) : ℝ) + (2⁻¹ : ℝ)) * (↑n)⁻¹)) =
        ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * (↑n)⁻¹) := by
    ring
  rw [hsub]
  ring_nf

end Fredholm1D
