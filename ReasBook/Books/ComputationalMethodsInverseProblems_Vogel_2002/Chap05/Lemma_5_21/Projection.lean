/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1_1
public import Mathlib.LinearAlgebra.Matrix.Diagonal

public section

open scoped Matrix

noncomputable section

namespace Matrix

/-- The Fourier-diagonal projection of `A` obtained by conjugating into the Chapter 5
Fourier basis, discarding off-diagonal entries, and conjugating back. -/
@[expose] def fourierDiagonalProjection {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (fourierMatrix n)ᴴ * diagonal (((fourierMatrix n) * A * (fourierMatrix n)ᴴ).diag) *
    fourierMatrix n

/-- The defining Fourier-diagonal formula for `Matrix.fourierDiagonalProjection`. -/
theorem fourierDiagonalProjection_def {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    fourierDiagonalProjection A =
      (fourierMatrix n)ᴴ * diagonal (((fourierMatrix n) * A * (fourierMatrix n)ᴴ).diag) *
        fourierMatrix n :=
  rfl

end Matrix
