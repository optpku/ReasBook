/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_8.Convolution2D

public section

open scoped BigOperators

namespace Matrix

/-- Definition 5.8. The two-dimensional discrete convolution product of an
integer-indexed kernel `t` with a finite complex array `f` has the coordinate
formula of `(5.25)`. -/
theorem discreteConvolution2D_apply {n_x n_y : ℕ} (t : ℤ → ℤ → ℂ)
    (f : Matrix (Fin n_x) (Fin n_y) ℂ) (i : Fin n_x) (j : Fin n_y) :
    Matrix.discreteConvolution2D t f i j =
      ∑ i' : Fin n_x, ∑ j' : Fin n_y,
        t (((i : ℕ) : ℤ) - (i' : ℕ)) (((j : ℕ) : ℤ) - (j' : ℕ)) * f i' j' := by
  -- Reduce the convolution entry to the HTTB-array backend at the vectorized
  -- coordinate `(j, i)`.
  rw [Matrix.discreteConvolution2D_def, Matrix.of_apply]
  -- Expand the matrix-vector product into an iterated finite sum over the two
  -- array indices, matching the textbook order.
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_comm]
  -- Evaluate each HTTB entry and normalize the swapped array coordinates.
  simp [Matrix.httb_apply]

end Matrix
