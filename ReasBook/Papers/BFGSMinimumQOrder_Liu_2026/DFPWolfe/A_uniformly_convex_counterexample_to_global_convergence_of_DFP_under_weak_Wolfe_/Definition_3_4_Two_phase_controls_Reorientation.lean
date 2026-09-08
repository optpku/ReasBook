module

public import ReasLib.LinearAlgebra.Matrix.OrientedEigenframe

public section

noncomputable section

open scoped Matrix

/- The legacy reorientation module remains a typed compatibility surface. -/
#check (OrientedEigenframe.lowVector :
  ℝ → ℝ → ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
#check (OrientedEigenframe.norm_lowVector : ∀ (a b d : ℝ)
  (g : EuclideanSpace ℝ (Fin 2)), a < d → ‖OrientedEigenframe.lowVector a b d g‖ = 1)
#check (OrientedEigenframe.lowVector_hasEigenvector : ∀ (a b d : ℝ)
  (g : EuclideanSpace ℝ (Fin 2)), a < d →
    Module.End.HasEigenvector
      ((Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
        (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)))
          (RealSymmetric2.matrix a b d)).toLinearMap
      (RealSymmetric2.low a b d) (OrientedEigenframe.lowVector a b d g))
#check (OrientedEigenframe.inner_lowVector_pos : ∀ (a b d : ℝ)
  (g : EuclideanSpace ℝ (Fin 2)),
    inner ℝ (RealSymmetric2.lowVector a b d) g ≠ 0 →
      0 < inner ℝ (OrientedEigenframe.lowVector a b d g) g)
#check (OrientedEigenframe.frame :
  ℝ → ℝ → ℝ → EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ)
#check (OrientedEigenframe.frame_mem_specialOrthogonalGroup : ∀ (a b d : ℝ)
  (g : EuclideanSpace ℝ (Fin 2)), a < d →
    OrientedEigenframe.frame a b d g ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
#check (OrientedEigenframe.frame_diagonalizes : ∀ (a b d : ℝ)
  (g : EuclideanSpace ℝ (Fin 2)), a < d →
    (OrientedEigenframe.frame a b d g).transpose * RealSymmetric2.matrix a b d *
        OrientedEigenframe.frame a b d g =
      Matrix.diagonal ![RealSymmetric2.low a b d, RealSymmetric2.high a b d])
