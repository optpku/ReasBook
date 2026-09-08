module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg

/-!
# Physical reconstruction of first-leg spectral data

The removable first-leg spectral factors reconstruct the physical updated
metric whenever their low-gradient and high-spectral coordinates are nonzero.
-/

public section

noncomputable section

open scoped Matrix

namespace DFP.FirstLeg

/-- Under the two nonvanishing factor hypotheses, the fixed first-leg frame
diagonalizes the updated metric pointwise. -/
theorem frameDiagonalization_of_ne (ε p h : ℝ)
    (hlow : (gradientFactors ε p h).1 ≠ 0)
    (hhigh : (spectralFactors ε p h).2 ≠ 0) :
    (frame ε p h).transpose * outputMetric ε p h * frame ε p h =
      Matrix.diagonal
        ![ε ^ 4 * (spectralFactors ε p h).1, (spectralFactors ε p h).2] := by
  let H := outputMetric ε p h
  let F := EuclideanPlane.frame
    (RealSymmetric2.lowVector (H 0 0) (H 0 1) (H 1 1))
  have hframe : frame ε p h = F := by
    simpa only [F, H] using frame_eq_lowEigenframe ε p h
  have hmatrix : H = RealSymmetric2.matrix (H 0 0) (H 0 1) (H 1 1) := by
    simpa only [H] using outputMetric_eq_symmetricMatrix ε p h
  have hdenom : RealSymmetric2.lowDenom (H 0 0) (H 0 1) (H 1 1) ≠ 0 := by
    simpa only [H] using
      lowDenom_ne_zero_of_gradientFactor_ne_zero ε p h hlow
  have hdiagonal := RealSymmetric2.frame_diagonalizes_of_lowDenom_ne_zero
    (H 0 0) (H 0 1) (H 1 1) hdenom
  have hspectrum := spectrumFactorization_of_high_ne_zero ε p h hhigh
  have hspectrumLow : RealSymmetric2.low (H 0 0) (H 0 1) (H 1 1) =
      ε ^ 4 * (spectralFactors ε p h).1 := by
    simpa only [eigenvalues_eq_lowHigh, H] using congrArg Prod.fst hspectrum
  have hspectrumHigh : RealSymmetric2.high (H 0 0) (H 0 1) (H 1 1) =
      (spectralFactors ε p h).2 := by
    simpa only [eigenvalues_eq_lowHigh, H] using congrArg Prod.snd hspectrum
  change (frame ε p h).transpose * H * frame ε p h = _
  rw [hframe]
  calc
    F.transpose * H * F =
        F.transpose * RealSymmetric2.matrix (H 0 0) (H 0 1) (H 1 1) * F :=
      congrArg (fun M ↦ F.transpose * M * F) hmatrix
    _ = Matrix.diagonal
        ![RealSymmetric2.low (H 0 0) (H 0 1) (H 1 1),
          RealSymmetric2.high (H 0 0) (H 0 1) (H 1 1)] := hdiagonal
    _ = Matrix.diagonal
        ![ε ^ 4 * (spectralFactors ε p h).1,
          (spectralFactors ε p h).2] := by
      rw [hspectrumLow, hspectrumHigh]

/-- Under the same hypotheses, conjugating the removable spectral diagonal
back by the fixed frame reconstructs the physical first-leg metric. -/
theorem metricReconstruction_of_ne (ε p h : ℝ)
    (hlow : (gradientFactors ε p h).1 ≠ 0)
    (hhigh : (spectralFactors ε p h).2 ≠ 0) :
    frame ε p h *
          Matrix.diagonal
            ![ε ^ 4 * (spectralFactors ε p h).1, (spectralFactors ε p h).2] *
        (frame ε p h).transpose =
      outputMetric ε p h := by
  let H := outputMetric ε p h
  let F := EuclideanPlane.frame
    (RealSymmetric2.lowVector (H 0 0) (H 0 1) (H 1 1))
  have hframe : frame ε p h = F := by
    simpa only [F, H] using frame_eq_lowEigenframe ε p h
  have hmatrix : H = RealSymmetric2.matrix (H 0 0) (H 0 1) (H 1 1) := by
    simpa only [H] using outputMetric_eq_symmetricMatrix ε p h
  have hdenom : RealSymmetric2.lowDenom (H 0 0) (H 0 1) (H 1 1) ≠ 0 := by
    simpa only [H] using
      lowDenom_ne_zero_of_gradientFactor_ne_zero ε p h hlow
  have hspectrum := spectrumFactorization_of_high_ne_zero ε p h hhigh
  have hspectrumLow : RealSymmetric2.low (H 0 0) (H 0 1) (H 1 1) =
      ε ^ 4 * (spectralFactors ε p h).1 := by
    simpa only [eigenvalues_eq_lowHigh, H] using congrArg Prod.fst hspectrum
  have hspectrumHigh : RealSymmetric2.high (H 0 0) (H 0 1) (H 1 1) =
      (spectralFactors ε p h).2 := by
    simpa only [eigenvalues_eq_lowHigh, H] using congrArg Prod.snd hspectrum
  have hreconstruct := RealSymmetric2.frame_reconstructs_of_lowDenom_ne_zero
    (H 0 0) (H 0 1) (H 1 1) hdenom
  change frame ε p h *
      Matrix.diagonal
        ![ε ^ 4 * (spectralFactors ε p h).1, (spectralFactors ε p h).2] *
      (frame ε p h).transpose = H
  rw [hframe]
  calc
    F * Matrix.diagonal
          ![ε ^ 4 * (spectralFactors ε p h).1,
            (spectralFactors ε p h).2] * F.transpose =
        RealSymmetric2.matrix (H 0 0) (H 0 1) (H 1 1) := by
      simpa only [hspectrumLow, hspectrumHigh] using hreconstruct
    _ = H := hmatrix.symm

end DFP.FirstLeg
