/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

noncomputable section

open scoped Matrix

namespace Tikhonov

universe u v

variable {m : Type u} {n : Type v}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]

/-- The finite-dimensional Tikhonov reconstruction
`((Kᵀ * K + α • 1)⁻¹ * Kᵀ) d`. -/
def reconstruction (K : Matrix m n ℝ) (α : ℝ) (d : EuclideanSpace ℝ m) :
    EuclideanSpace ℝ n :=
  Matrix.toEuclideanLin ((Kᵀ * K + α • (1 : Matrix n n ℝ))⁻¹ * Kᵀ) d

/-- The defining formula for `Tikhonov.reconstruction`. -/
theorem reconstruction_eq (K : Matrix m n ℝ) (α : ℝ) (d : EuclideanSpace ℝ m) :
    reconstruction K α d =
      Matrix.toEuclideanLin ((Kᵀ * K + α • (1 : Matrix n n ℝ))⁻¹ * Kᵀ) d := by
  simp [reconstruction]

end Tikhonov
