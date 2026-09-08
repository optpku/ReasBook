module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawCanonicalFrameSlopeTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualSourceCertificate

public section

noncomputable section

open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
This companion is the source-facing assembly boundary for a local projection-domain
kernel.  A source calculation may remain in the mixed bracket normal form; the
adapter transports it to the canonical frame package and fills the removable
zero-scale and zero-radius branches without exposing the frame construction.
-/

/-- Helper for Infrastructure I.16a (Appendix Lemma A.6): a projection-domain mixed-bracket
kernel, together with its removable cover and continuity data, produces the
canonical filled center-residual source certificate. -/
noncomputable def CanonicalFrameKernelDataOn.toSourceCertificate_of_projectionDomain
    {β B radius : ℝ}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (hradius : 0 < radius)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hD : ∀ θ r, D θ r → mixedRawProjectionDomain θ r)
    (hcover : ∀ θ, θ ∈ parameterSet β B → ∀ r : ℝ, |r| < radius →
      θ.1 = 0 ∨ r = 0 ∨ D θ r)
    (hkernel : ∀ θ r, D θ r →
      mixedCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r)
    (hK : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-radius) radius)) :
    CenterResidualSourceCertificate β B
      (centerResidualKernelFilledQuotient K) :=
  FrameKernelDataOn.toLocalSourceCertificate_of_removableCover
    (CanonicalFrameKernelDataOn.of_projectionDomain_of_mixedKernel hD hkernel)
    hradius hscale hcover hK

end DFP.TwoLeg.Mixed
