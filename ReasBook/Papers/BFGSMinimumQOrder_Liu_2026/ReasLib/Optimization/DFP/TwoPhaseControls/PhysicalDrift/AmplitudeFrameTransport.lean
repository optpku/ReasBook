module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.PhysicalAmplitudeFrameCertificate
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeProjectionTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.PhysicalAmplitudeFrameCertificate
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeProjectionTransport

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.TwoLeg.Mixed

/-- Helper for Appendix Lemma A.6: a pathwise frame certificate packages the raw
amplitude, frame orientation, canonical coordinates, and low-coordinate target used
to transport a physical amplitude through a product-filter germ. -/
structure PhysicalAmplitudeFramePathCertificate
    (K : Set (ℝ × ℝ × ℝ)) where
  rawAmplitude : (ℝ × ℝ × ℝ) × ℝ → ℝ
  frame : (ℝ × ℝ × ℝ) × ℝ → Matrix (Fin 2) (Fin 2) ℝ
  vector : (ℝ × ℝ × ℝ) × ℝ → Fin 2 → ℝ
  metricA : (ℝ × ℝ × ℝ) × ℝ → ℝ
  metricB : (ℝ × ℝ × ℝ) × ℝ → ℝ
  metricD : (ℝ × ℝ × ℝ) × ℝ → ℝ
  coordinateQ : (ℝ × ℝ × ℝ) × ℝ → ℝ
  coordinateU : (ℝ × ℝ × ℝ) × ℝ → ℝ
  eventual : ∀ θ, θ ∈ K → ∀ᶠ z in 𝓝 (θ, 0),
    (observableMap z.1.1 (input z.1 z.2)).amplitudeRatio = rawAmplitude z ∧
      rawAmplitude z = (frame z).transpose.mulVec (vector z) 0 ∧
      frame z = OrientedEigenframe.frame (metricA z) (metricB z) (metricD z)
        (WithLp.toLp 2 (vector z)) ∧
      ((frame z = EuclideanPlane.frame
          (RealSymmetric2.lowVector (metricA z) (metricB z) (metricD z)) ∧
          (EuclideanPlane.frame
            (RealSymmetric2.lowVector (metricA z) (metricB z) (metricD z))).transpose.mulVec
            (vector z) = ![coordinateQ z, coordinateU z]) ∨
        (frame z = -EuclideanPlane.frame
          (RealSymmetric2.lowVector (metricA z) (metricB z) (metricD z)) ∧
          (EuclideanPlane.frame
            (RealSymmetric2.lowVector (metricA z) (metricB z) (metricD z))).transpose.mulVec
            (vector z) = -![coordinateQ z, coordinateU z])) ∧
      0 < coordinateQ z ∧
      coordinateQ z = (independentRadiusSecondGradient (z.1, z.2)).1

/-- Appendix Lemma A.6: a pathwise frame certificate yields the uncurried
physical-to-normalized amplitude equality required by germ transport. -/
theorem PhysicalAmplitudeFramePathCertificate.uncurry_eventuallyEq_secondGradientLow
    {K : Set (ℝ × ℝ × ℝ)}
    (certificate : PhysicalAmplitudeFramePathCertificate K) :
    ∀ θ, θ ∈ K →
      Function.uncurry
          (fun η r ↦ (observableMap η.1 (input η r)).amplitudeRatio) =ᶠ[𝓝 (θ, 0)]
        Function.uncurry
          (fun η r ↦ (independentRadiusSecondGradient (η, r)).1) := by
  intro θ hθ
  filter_upwards [certificate.eventual θ hθ] with z hz
  rcases hz with ⟨hraw, hcoordinate, hframe, hsigned, hq, hqtarget⟩
  simpa only [Function.uncurry] using
    (physicalAmplitude_eq_independentRadiusSecondGradientLow_of_pointwiseCertificate
      z.1 z.2 (certificate.metricA z) (certificate.metricB z) (certificate.metricD z)
      (certificate.coordinateQ z) (certificate.coordinateU z)
      (certificate.rawAmplitude z) (certificate.frame z) (certificate.vector z)
      hraw hcoordinate hframe hsigned hq hqtarget)

end DFP.TwoLeg.Mixed
