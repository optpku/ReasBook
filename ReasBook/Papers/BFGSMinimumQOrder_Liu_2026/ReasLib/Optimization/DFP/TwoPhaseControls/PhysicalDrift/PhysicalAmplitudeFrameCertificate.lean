module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.SecondGradientFrameCoordinates
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeProjectionBridge
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.SecondGradientFrameCoordinates
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeProjectionBridge

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoLeg.Mixed

/-!
This is the pointwise boundary between the physical amplitude evaluator and the
normalized second-gradient coordinate.  The raw evaluator value, its frame-coordinate
realization, and the signed canonical-frame choice are all explicit hypotheses.
-/

/-- Helper for Appendix Lemma A.6: an explicit raw-amplitude and signed-frame certificate
    identifies the physical amplitude with the normalized second-gradient low coordinate. -/
theorem physicalAmplitude_eq_independentRadiusSecondGradientLow_of_pointwiseCertificate
    (θ : ℝ × ℝ × ℝ) (r a b d q u : ℝ)
    (rawAmplitude : ℝ) (F : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ)
    (hraw :
      (observableMap θ.1 (input θ r)).amplitudeRatio = rawAmplitude)
    (hrawCoordinate : rawAmplitude = F.transpose.mulVec v 0)
    (hFOriented : F = OrientedEigenframe.frame a b d (WithLp.toLp 2 v))
    (hsigned :
      (F = EuclideanPlane.frame (RealSymmetric2.lowVector a b d) ∧
        (EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose.mulVec v =
          ![q, u]) ∨
      (F = -EuclideanPlane.frame (RealSymmetric2.lowVector a b d) ∧
        (EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose.mulVec v =
          -![q, u]))
    (hq : 0 < q)
    (hqtarget : q = (independentRadiusSecondGradient (θ, r)).1) :
    (observableMap θ.1 (input θ r)).amplitudeRatio =
      (independentRadiusSecondGradient (θ, r)).1 := by
  have hcoordinate : F.transpose.mulVec v 0 = q := by
    rcases hsigned with hpositive | hnegative
    · have hbridge := orientedEigenframe_lowCoordinate_eq_of_positive_coordinate
        a b d q u v hpositive.2 hq
      rw [hFOriented]
      exact hbridge
    · exact orientedLowCoordinate_eq_of_signedFrameCertificate
        a b d q u v F (Or.inr hnegative)
  calc
    (observableMap θ.1 (input θ r)).amplitudeRatio = rawAmplitude := hraw
    _ = F.transpose.mulVec v 0 := hrawCoordinate
    _ = q := hcoordinate
    _ = (independentRadiusSecondGradient (θ, r)).1 := hqtarget

end DFP.TwoLeg.Mixed
