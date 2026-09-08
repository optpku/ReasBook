module

public import ReasLib.LinearAlgebra.Matrix.RealSymmetric2.Eigenframe
public import ReasLib.Geometry.Euclidean.Plane.Rotation

public section

noncomputable section

open scoped Matrix

namespace OrientedEigenframe

/-- Choose the explicit low eigenvector with sign directed toward the updated gradient. -/
def lowVector (a b d : ℝ) (g : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  if 0 < inner ℝ (RealSymmetric2.lowVector a b d) g then
    RealSymmetric2.lowVector a b d
  else
    -RealSymmetric2.lowVector a b d

/-- On the explicit spectral chart, the gradient-oriented low eigenvector has unit norm. -/
theorem norm_lowVector (a b d : ℝ) (g : EuclideanSpace ℝ (Fin 2))
    (hchart : a < d) :
    ‖lowVector a b d g‖ = 1 := by
  -- Start from the unit norm of the unoriented low eigenvector on the chart.
  have hnorm := RealSymmetric2.norm_lowVector a b d hchart
  -- The orientation changes only the sign, which does not change the norm.
  rw [lowVector]
  split_ifs
  · exact hnorm
  · simpa only [norm_neg] using hnorm

/-- On the explicit spectral chart, changing the sign preserves the low-eigenvector
equation and nonvanishing condition. -/
theorem lowVector_hasEigenvector (a b d : ℝ) (g : EuclideanSpace ℝ (Fin 2))
    (hchart : a < d) :
    Module.End.HasEigenvector
      ((Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
        (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)))
          (RealSymmetric2.matrix a b d)).toLinearMap
      (RealSymmetric2.low a b d) (lowVector a b d g) := by
  -- Separate the canonical eigenvector certificate into eigenspace membership
  -- and nonvanishing before transporting both facts through the sign choice.
  have hbase := RealSymmetric2.lowVector_hasEigenvector a b d hchart
  rw [lowVector]
  split_ifs
  · exact hbase
  · rw [Module.End.hasEigenvector_iff]
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      rw [map_neg, hbase.apply_eq_smul, smul_neg]
    · exact neg_ne_zero.mpr hbase.2

/-- If the updated gradient is not orthogonal to the original low eigenvector, the
chosen low eigenvector has strictly positive inner product with it. -/
theorem inner_lowVector_pos (a b d : ℝ) (g : EuclideanSpace ℝ (Fin 2))
    (h_ne : inner ℝ (RealSymmetric2.lowVector a b d) g ≠ 0) :
    0 < inner ℝ (lowVector a b d g) g := by
  -- Split on the defining orientation test; the positive branch is immediate.
  rw [lowVector]
  split_ifs with hpos
  · exact hpos
  · -- In the remaining branch, nonorthogonality upgrades nonpositivity to
    -- strict negativity, which changes to positivity after negating the vector.
    have hneg : inner ℝ (RealSymmetric2.lowVector a b d) g < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) h_ne
    rw [inner_neg_left]
    exact neg_pos.mpr hneg

/-- The positively oriented frame determined by the gradient-oriented low eigenvector. -/
def frame (a b d : ℝ) (g : EuclideanSpace ℝ (Fin 2)) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  EuclideanPlane.frame (lowVector a b d g)

/-- On the explicit spectral chart, the gradient-oriented frame is special orthogonal. -/
theorem frame_mem_specialOrthogonalGroup (a b d : ℝ)
    (g : EuclideanSpace ℝ (Fin 2)) (hchart : a < d) :
    frame a b d g ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  -- The canonical oriented frame is special orthogonal exactly when its first
  -- column has unit norm, already established for the sign-oriented vector.
  rw [frame, EuclideanPlane.frame_mem_specialOrthogonalGroup_iff]
  exact norm_lowVector a b d g hchart

/-- In the gradient-oriented frame, the symmetric matrix is diagonal with its low
eigenvalue first and high eigenvalue second. -/
theorem frame_diagonalizes (a b d : ℝ) (g : EuclideanSpace ℝ (Fin 2))
    (hchart : a < d) :
    (frame a b d g).transpose * RealSymmetric2.matrix a b d * frame a b d g =
      Matrix.diagonal ![RealSymmetric2.low a b d, RealSymmetric2.high a b d] := by
  -- Reduce to the fixed eigenframe in the positive orientation branch.
  rw [frame, lowVector]
  split_ifs
  · exact RealSymmetric2.frame_diagonalizes a b d hchart
  · -- Negating the first column also negates its perpendicular, so the
    -- entire frame changes by one global matrix sign.
    have hframeZero (e : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
        EuclideanPlane.frame e i 0 = e i := by
      have hcolumn := congrArg (fun v : Fin 2 → ℝ ↦ v i)
        (EuclideanPlane.frame_mulVec e 1 0)
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hcolumn
    have hframeOne (e : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
        EuclideanPlane.frame e i 1 = EuclideanPlane.perp e i := by
      have hcolumn := congrArg (fun v : Fin 2 → ℝ ↦ v i)
        (EuclideanPlane.frame_mulVec e 0 1)
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hcolumn
    have hframeNegZero (e : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
        EuclideanPlane.frame (-e) i 0 = (-EuclideanPlane.frame e) i 0 := by
      simp only [Matrix.neg_apply, hframeZero, WithLp.ofLp_neg, Pi.neg_apply]
    have hframeNegOne (e : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
        EuclideanPlane.frame (-e) i 1 = (-EuclideanPlane.frame e) i 1 := by
      simp only [Matrix.neg_apply, hframeOne, map_neg, WithLp.ofLp_neg, Pi.neg_apply]
    have hframeNeg : EuclideanPlane.frame (-RealSymmetric2.lowVector a b d) =
        -EuclideanPlane.frame (RealSymmetric2.lowVector a b d) := by
      ext i j
      fin_cases j
      · simpa using hframeNegZero (RealSymmetric2.lowVector a b d) i
      · simpa using hframeNegOne (RealSymmetric2.lowVector a b d) i
    rw [hframeNeg]
    -- The two frame signs cancel in the conjugation.
    simpa only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using
      RealSymmetric2.frame_diagonalizes a b d hchart

end OrientedEigenframe
