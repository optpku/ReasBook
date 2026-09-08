module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.FrameAngleArctanGermCertificate
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.FrameAngleArctanGermCertificate
import all ReasLib.Geometry.Euclidean.Plane.SignedAngle

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.TwoLeg.Mixed

/-!
This companion exposes the scalar tangent chart hidden in the raw relative-frame
observable.  The frame algebra is kept in a named definition, so a later source
calculation only has to provide regularity and the first radius derivative of this
scalar quotient.
-/

/-- Helper for Appendix Lemma A.6: the raw two-leg relative frame matrix is the
    product of the two oriented eigenframes used by `mixedIndependentRawFrameAngle`. -/
def mixedIndependentRawFrameAngleMatrix (b r p h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * r ^ 2, h]
  let g₀ : Fin 2 → ℝ := ![(1 : ℝ), p * r]
  let firstStep := independentRawStep H₀ g₀ (TwoPhaseControls.first b)
  let firstFrame := OrientedEigenframe.frame
    (firstStep.1 0 0) (firstStep.1 0 1) (firstStep.1 1 1)
    (WithLp.toLp 2 firstStep.2)
  let H₁ := firstFrame.transpose * firstStep.1 * firstFrame
  let g₁ := firstFrame.transpose *ᵥ firstStep.2
  let secondStep := independentRawStep H₁ g₁ (TwoPhaseControls.second b)
  let secondFrame := OrientedEigenframe.frame
    (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
    (WithLp.toLp 2 secondStep.2)
  firstFrame * secondFrame

/-- Helper for Appendix Lemma A.6: the raw relative-frame tangent coordinate is
    the lower-left entry divided by the upper-left entry. -/
def mixedIndependentRawFrameAngleSlope (b r p h : ℝ) : ℝ :=
  let M := mixedIndependentRawFrameAngleMatrix b r p h
  M 1 0 / M 0 0

/-- Helper for Appendix Lemma A.6: the raw frame-angle observable is the arctangent
    of its explicit relative-frame tangent coordinate. -/
theorem mixedIndependentRawFrameAngle_eq_arctan_slope (b r p h : ℝ) :
    mixedIndependentRawFrameAngle b r p h =
      Real.arctan (mixedIndependentRawFrameAngleSlope b r p h) := by
  simp only [mixedIndependentRawFrameAngle, mixedIndependentRawFrameAngleSlope,
    mixedIndependentRawFrameAngleMatrix, EuclideanPlane.SignedAngle.coordinate]

/-- Helper for Appendix Lemma A.6: the raw frame-angle tangent and angle along the
    canonical mixed input path. -/
def mixedIndependentRawFrameAngleSlopeAlongInput
    (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  mixedIndependentRawFrameAngleSlope θ.1 r
    (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)

/-- Helper for Appendix Lemma A.6: the canonical mixed raw frame angle is the
    arctangent of the pathwise relative-frame tangent. -/
theorem mixedIndependentRawFrameAngleAlongInput_eq_arctan_slope
    (θ : ℝ × ℝ × ℝ) (r : ℝ) :
    mixedIndependentRawFrameAngle θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
      Real.arctan (mixedIndependentRawFrameAngleSlopeAlongInput θ r) := by
  exact mixedIndependentRawFrameAngle_eq_arctan_slope θ.1 r
    (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)

/-- Helper for Appendix Lemma A.6: the relative-frame tangent vanishes at the
    removable radius of the canonical mixed input. -/
theorem mixedIndependentRawFrameAngle_zero (b : ℝ) :
    mixedIndependentRawFrameAngle b 0 2 1 = 0 := by
  unfold mixedIndependentRawFrameAngle
  dsimp only
  have hH :
      Matrix.diagonal ![(1 : ℝ) * 2 * (0 : ℝ) ^ 2, 1] =
        Matrix.diagonal ![(0 : ℝ), 1] := by
    simp
  have hg : (![1, (2 : ℝ) * 0] : Fin 2 → ℝ) = ![(1 : ℝ), 0] := by
    ext i
    fin_cases i
    · simp
    · simp
  rw [hH, hg]
  have hfirstStep := independentRawStep_zeroRadius_base (TwoPhaseControls.first b)
  rw [hfirstStep]
  have hbaseFrame :
      OrientedEigenframe.frame
          ((Matrix.diagonal ![(0 : ℝ), 1]) 0 0)
          ((Matrix.diagonal ![(0 : ℝ), 1]) 0 1)
          ((Matrix.diagonal ![(0 : ℝ), 1]) 1 1)
          (WithLp.toLp 2 ![(1 : ℝ), 0]) = 1 := by
    simpa [Matrix.diagonal_apply, Fin.isValue] using orientedEigenframe_zeroRadius_frame
  rw [hbaseFrame]
  have hsecondStep := independentRawStep_zeroRadius_conjugated
    (TwoPhaseControls.second b)
  rw [hsecondStep]
  rw [hbaseFrame]
  simp [EuclideanPlane.SignedAngle.coordinate_one]

/-- Helper for Appendix Lemma A.6: the relative-frame tangent vanishes at the
    removable radius of the canonical mixed input. -/
theorem mixedIndependentRawFrameAngleSlopeAlongInput_zero
    (θ : ℝ × ℝ × ℝ) :
    mixedIndependentRawFrameAngleSlopeAlongInput θ 0 = 0 := by
  have hangle := mixedIndependentRawFrameAngle_zero θ.1
  have hangleSlope := mixedIndependentRawFrameAngle_eq_arctan_slope θ.1 0 2 1
  have hslope : mixedIndependentRawFrameAngleSlope θ.1 0 2 1 = 0 := by
    have harctan : Real.arctan (mixedIndependentRawFrameAngleSlope θ.1 0 2 1) = 0 := by
      rw [← hangleSlope]
      exact hangle
    exact Real.arctan_eq_zero_iff.mp harctan
  simpa [mixedIndependentRawFrameAngleSlopeAlongInput] using hslope

/-- Appendix Lemma A.6: a source certificate for the scalar relative-frame tangent
    yields the uniform `[0, -3]` independent-radius germ of the raw frame angle. -/
theorem mixedIndependentRawFrameAngleAlongInput_truncatedGerm_of_slopeCertificate
    {K : Set (ℝ × ℝ × ℝ)}
    (hregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 2
        (Function.uncurry mixedIndependentRawFrameAngleSlopeAlongInput) (θ, 0))
    (hlinear : ∀ θ, θ ∈ K →
      deriv (mixedIndependentRawFrameAngleSlopeAlongInput θ) 0 = -3) :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ mixedIndependentRawFrameAngle θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)) K 2
      (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) := by
  have hzero : ∀ θ, θ ∈ K →
      mixedIndependentRawFrameAngleSlopeAlongInput θ 0 = 0 := by
    intro θ hθ
    exact mixedIndependentRawFrameAngleSlopeAlongInput_zero θ
  have hslope := independentRadiusTruncatedGerm_of_arctan_zero_slope
    (f := mixedIndependentRawFrameAngleSlopeAlongInput)
    (K := K) (a := fun _θ ↦ (-3 : ℝ)) hregular hzero hlinear
  have hfun :
      (fun θ r ↦ mixedIndependentRawFrameAngle θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)) =
        (fun θ r ↦ Real.arctan (mixedIndependentRawFrameAngleSlopeAlongInput θ r)) := by
    funext θ r
    exact mixedIndependentRawFrameAngleAlongInput_eq_arctan_slope θ r
  rw [hfun]
  simpa using hslope

end DFP.TwoLeg.Mixed
