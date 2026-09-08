module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AngleQuadraticTransport

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-- Infrastructure for Appendix Lemma A.6: a scalar raw slope and its frame-angle
observable are related by an explicit arctangent identity, while regularity and
the zero/derivative data remain source-facing certificate fields. -/
structure FrameAngleArctanGermCertificate
    (rawSlope frameAngle : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (K : Set (ℝ × ℝ × ℝ)) where
  coefficient : (ℝ × ℝ × ℝ) → ℝ
  regularity : ∀ θ, θ ∈ K →
    ContDiffAt ℝ 2 (Function.uncurry rawSlope) (θ, 0)
  zero : ∀ θ, θ ∈ K → rawSlope θ 0 = 0
  derivative : ∀ θ, θ ∈ K → deriv (rawSlope θ) 0 = coefficient θ
  frameAngle_eq_arctan : ∀ θ r, frameAngle θ r = Real.arctan (rawSlope θ r)

/-- Infrastructure for Appendix Lemma A.6: the scalar slope certificate produces
the quadratic independent-radius germ for the frame-angle observable. -/
theorem FrameAngleArctanGermCertificate.toIndependentRadiusTruncatedGerm
    {rawSlope frameAngle : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {K : Set (ℝ × ℝ × ℝ)}
    (certificate : FrameAngleArctanGermCertificate rawSlope frameAngle K) :
    IndependentRadiusTruncatedGerm frameAngle K 2
      (fun n θ ↦ (![0, certificate.coefficient θ] : Fin 2 → ℝ) n) := by
  have hraw := independentRadiusTruncatedGerm_of_arctan_zero_slope
    certificate.regularity certificate.zero certificate.derivative
  refine ⟨?_, ?_⟩
  · intro θ hθ
    have hregular := hraw.regularity θ hθ
    have hfun :
        Function.uncurry frameAngle =
          (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
            Real.arctan (Function.uncurry rawSlope z)) := by
      funext z
      exact certificate.frameAngle_eq_arctan z.1 z.2
    rw [hfun]
    exact hregular
  · intro n θ hθ
    have hcoeff := hraw.coefficient_eq n θ hθ
    have hframe :
        (FiniteTaylorJet.ofFunction ℝ 2 (frameAngle θ) 0).scalarCoeff n.castSucc =
          (FiniteTaylorJet.ofFunction ℝ 2
            (fun r ↦ Real.arctan (rawSlope θ r)) 0).scalarCoeff n.castSucc := by
      congr 2
      funext r
      exact certificate.frameAngle_eq_arctan θ r
    rw [hframe]
    exact hcoeff

/-- Infrastructure for Appendix Lemma A.6: the same adapter exposes the raw
slope germ separately, which is useful before applying frame-angle transport. -/
theorem FrameAngleArctanGermCertificate.rawSlope_germ
    {rawSlope frameAngle : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {K : Set (ℝ × ℝ × ℝ)}
    (certificate : FrameAngleArctanGermCertificate rawSlope frameAngle K) :
    ∀ θ ∈ K, rawSlope θ 0 = 0 ∧ deriv (rawSlope θ) 0 = certificate.coefficient θ := by
  intro θ hθ
  exact ⟨certificate.zero θ hθ, certificate.derivative θ hθ⟩

end DFP.TwoLeg.Mixed
