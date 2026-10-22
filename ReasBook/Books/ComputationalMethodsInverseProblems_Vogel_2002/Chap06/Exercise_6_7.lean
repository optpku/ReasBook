/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Example_6_2.DiffusionMatrices

public section

open OneDimensionalDiffusion

/-- Exercise 6.7. The `j`th least-squares gradient entry equals the negative
mesh-scaled product of the `j`th discrete first differences of `u` and `z`. -/
theorem leastSquaresGradientEntry_eq_negDifferenceProduct
    (n : ℕ) (u z : Fin (n + 1) → ℝ) (j : Fin n) :
    -((n + 1 : ℝ) * Matrix.mulVec (Matrix.transpose (differenceMatrix n)) u j *
        Matrix.mulVec (Matrix.transpose (differenceMatrix n)) z j) =
      -((n + 1 : ℝ) * (u (Fin.castSucc j) - u j.succ) *
        (z (Fin.castSucc j) - z j.succ)) := by
  simp [differenceMatrixTranspose_mulVec_apply]
