module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawObservableZero
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawObservableZero

public section

noncomputable section

open scoped EuclideanSpace Matrix Topology

namespace DFP.TwoLeg.Mixed

/-!
The zero-radius observable is the removable base branch used by the mixed physical
drift.  This companion keeps the raw-step and oriented-frame reductions in one
proof interface, so downstream quotient arguments can handle the branch by rewriting.
-/

/-- Helper for Appendix Lemma A.6: at zero radius both raw steps are stationary at the
    diagonal base, so the full center displacement vanishes. -/
theorem observableMap_zeroRadius_fullCenterDisplacement (b : ℝ) :
    (observableMap b (0, 2, 1)).fullCenterDisplacement = 0 := by
  dsimp [observableMap]
  norm_num
  have hstep₁ :
      rawObservableStep (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0]
          (TwoPhaseControls.first b) =
        (Matrix.diagonal ![(0 : ℝ), 1], ![(1 : ℝ), 0], 0) := by
    simpa using rawObservableStep_zeroRadius_scaled 1 1 2 (TwoPhaseControls.first b)
  simp_rw [hstep₁]
  have hframe₁ :
      OrientedEigenframe.frame
          ((Matrix.diagonal ![(0 : ℝ), 1]) 0 0)
          ((Matrix.diagonal ![(0 : ℝ), 1]) 0 1)
          ((Matrix.diagonal ![(0 : ℝ), 1]) 1 1)
          (WithLp.toLp 2 ![(1 : ℝ), 0]) = 1 := by
    simpa [Matrix.diagonal_apply, Fin.isValue] using orientedEigenframe_zeroRadius_frame
  simp_rw [hframe₁]
  have hstep₂ :
      rawObservableStep
          ((1 : Matrix (Fin 2) (Fin 2) ℝ).transpose *
            Matrix.diagonal ![(0 : ℝ), 1] * 1)
          ((1 : Matrix (Fin 2) (Fin 2) ℝ).transpose *ᵥ ![(1 : ℝ), 0])
          (TwoPhaseControls.second b) =
        (Matrix.diagonal ![(0 : ℝ), 1], ![(1 : ℝ), 0], 0) := by
    rw [rawObservableStep_identity_conjugation]
    exact rawObservableStep_zeroRadius_base (TwoPhaseControls.second b)
  simp_rw [hstep₂]
  simp

/-- Helper for Appendix Lemma A.6: the zero-radius physical amplitude has its unit
    removable value. -/
theorem observableMap_zeroRadius_amplitudeRatio (b : ℝ) :
    (observableMap b (0, 2, 1)).amplitudeRatio = 1 := by
  dsimp [observableMap]
  norm_num
  have hstep₁ :
      rawObservableStep (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0]
          (TwoPhaseControls.first b) =
        (Matrix.diagonal ![(0 : ℝ), 1], ![(1 : ℝ), 0], 0) := by
    simpa using rawObservableStep_zeroRadius_scaled 1 1 2 (TwoPhaseControls.first b)
  simp_rw [hstep₁]
  have hframe₁ :
      OrientedEigenframe.frame
          ((Matrix.diagonal ![(0 : ℝ), 1]) 0 0)
          ((Matrix.diagonal ![(0 : ℝ), 1]) 0 1)
          ((Matrix.diagonal ![(0 : ℝ), 1]) 1 1)
          (WithLp.toLp 2 ![(1 : ℝ), 0]) = 1 := by
    simpa [Matrix.diagonal_apply, Fin.isValue] using orientedEigenframe_zeroRadius_frame
  simp_rw [hframe₁]
  have hstep₂ :
      rawObservableStep
          ((1 : Matrix (Fin 2) (Fin 2) ℝ).transpose *
            Matrix.diagonal ![(0 : ℝ), 1] * 1)
          ((1 : Matrix (Fin 2) (Fin 2) ℝ).transpose *ᵥ ![(1 : ℝ), 0])
          (TwoPhaseControls.second b) =
        (Matrix.diagonal ![(0 : ℝ), 1], ![(1 : ℝ), 0], 0) := by
    rw [rawObservableStep_identity_conjugation]
    exact rawObservableStep_zeroRadius_base (TwoPhaseControls.second b)
  simp_rw [hstep₂]
  simp_rw [hframe₁]
  simp

/-- Helper for Appendix Lemma A.6: the three scalar/vector projections at the
    removable zero-radius base reduce simultaneously to `(1, 0, 0)`. -/
theorem observableMap_zeroRadius_projectionData (b : ℝ) :
    ((observableMap b (0, 2, 1)).amplitudeRatio,
      (observableMap b (0, 2, 1)).frameAngleIncrement,
      (observableMap b (0, 2, 1)).fullCenterDisplacement) = (1, 0, 0) := by
  dsimp [observableMap]
  norm_num
  have hstep₁ :
      rawObservableStep (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0]
          (TwoPhaseControls.first b) =
        (Matrix.diagonal ![(0 : ℝ), 1], ![(1 : ℝ), 0], 0) := by
    simpa using rawObservableStep_zeroRadius_scaled 1 1 2 (TwoPhaseControls.first b)
  simp_rw [hstep₁]
  have hframe₁ :
      OrientedEigenframe.frame
          ((Matrix.diagonal ![(0 : ℝ), 1]) 0 0)
          ((Matrix.diagonal ![(0 : ℝ), 1]) 0 1)
          ((Matrix.diagonal ![(0 : ℝ), 1]) 1 1)
          (WithLp.toLp 2 ![(1 : ℝ), 0]) = 1 := by
    simpa [Matrix.diagonal_apply, Fin.isValue] using orientedEigenframe_zeroRadius_frame
  simp_rw [hframe₁]
  have hstep₂ :
      rawObservableStep
          ((1 : Matrix (Fin 2) (Fin 2) ℝ).transpose *
            Matrix.diagonal ![(0 : ℝ), 1] * 1)
          ((1 : Matrix (Fin 2) (Fin 2) ℝ).transpose *ᵥ ![(1 : ℝ), 0])
          (TwoPhaseControls.second b) =
        (Matrix.diagonal ![(0 : ℝ), 1], ![(1 : ℝ), 0], 0) := by
    rw [rawObservableStep_identity_conjugation]
    exact rawObservableStep_zeroRadius_base (TwoPhaseControls.second b)
  simp_rw [hstep₂, hframe₁]
  simp [EuclideanPlane.SignedAngle.coordinate_one]

end DFP.TwoLeg.Mixed
