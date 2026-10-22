/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2_2.Reconstruction
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1.Blur2D

public section

noncomputable section

section

/-- The vectorization of a discrete image obtained by pairing row and column
indices. -/
def imageAsVector {n_x n_y : ℕ}
    (f : Matrix (Fin n_x) (Fin n_y) ℝ) : EuclideanSpace ℝ (Fin n_x × Fin n_y) :=
  WithLp.toLp 2 (fun p : Fin n_x × Fin n_y ↦ f p.1 p.2)

/-- The matrix realization of a four-index discrete blur kernel on vectorized
images. -/
def imageDeblurringBlurMatrix {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ) :
    Matrix (Fin n_x × Fin n_y) (Fin n_x × Fin n_y) ℝ :=
  fun p q : Fin n_x × Fin n_y ↦ psf p.1 q.1 p.2 q.2

/-- The Tikhonov residual family used by the minimum-bound method for a
vectorized discrete image-deblurring datum. -/
def imageDeblurringResidualFamily {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (dObs : Matrix (Fin n_x) (Fin n_y) ℝ) :
    ℝ → EuclideanSpace ℝ (Fin n_x × Fin n_y) :=
  let K := imageDeblurringBlurMatrix psf
  let d := imageAsVector dObs
  fun α ↦ K.toEuclideanLin (Tikhonov.reconstruction K α d) - d

/-- Evaluating `imageDeblurringResidualFamily` gives the Tikhonov residual of
the vectorized discrete image-deblurring datum. -/
@[simp] theorem imageDeblurringResidualFamily_eq {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (dObs : Matrix (Fin n_x) (Fin n_y) ℝ) (α : ℝ) :
    imageDeblurringResidualFamily psf dObs α =
      (imageDeblurringBlurMatrix psf).toEuclideanLin
          (Tikhonov.reconstruction (imageDeblurringBlurMatrix psf) α (imageAsVector dObs)) -
        imageAsVector dObs := by
  simp [imageDeblurringResidualFamily]

/-- Applying the image-deblurring blur matrix to a vectorized image recovers
`Blur2D.discreteBlur`. -/
theorem imageDeblurringBlurMatrix_apply_imageAsVector {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (f : Matrix (Fin n_x) (Fin n_y) ℝ) :
    (imageDeblurringBlurMatrix psf).toEuclideanLin (imageAsVector f) =
      imageAsVector (Blur2D.discreteBlur psf f) := by
  apply WithLp.ofLp_injective
  ext p
  rcases p with ⟨i, j⟩
  -- Unfold the vectorized matrix action and reindex the sum over pairs as nested sums.
  change
    Matrix.mulVec (imageDeblurringBlurMatrix psf)
        (fun p : Fin n_x × Fin n_y ↦ f p.1 p.2) (i, j) =
      Blur2D.discreteBlur psf f i j
  rw [Blur2D.discreteBlur_apply]
  change (∑ x : Fin n_x × Fin n_y, psf i x.1 j x.2 * f x.1 x.2) = _
  rw [← Finset.univ_product_univ, Finset.sum_product]

end
