module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.BranchAssembly
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterQuotientCompactBound
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualAdapter

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-- Infrastructure for Appendix Lemma A.6: a source-facing center-residual
certificate records the removable branches, the punctured cubic quotient, and
a continuous compact kernel representing that quotient on one radius tube. -/
structure CenterResidualSourceCertificate
    (β B : ℝ) (Q : (ℝ × ℝ × ℝ) → ℝ → ℝ) where
  kernel : (ℝ × ℝ × ℝ) → ℝ → ℝ
  radius : ℝ
  radius_pos : 0 < radius
  scale_zero : ∀ θ r, θ.1 = 0 →
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
      centerDriftCoefficient θ * r ^ 2 = 0
  punctured_factorization : ∀ θ r, θ.1 ≠ 0 → r ≠ 0 →
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
      centerDriftCoefficient θ * r ^ 2 =
      (θ.1 * r ^ (3 : ℕ)) • Q θ r
  kernel_continuous : ContinuousOn
    (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ kernel z.1 z.2)
    (parameterSet β B ×ˢ Set.Icc (-radius) radius)
  quotient_eq_kernel : ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < radius →
    Q θ r = kernel θ r

/-- Infrastructure for Appendix Lemma A.6: the source certificate yields the
uniform mixed-variable cubic bound for the concrete full-center residual. -/
theorem CenterResidualSourceCertificate.uniformBound
    {β B : ℝ} {Q : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (certificate : CenterResidualSourceCertificate β B Q) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
      ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ 2‖ ≤
      C * |θ.1| * |r| ^ (3 : ℝ) := by
  have hfactor : ∀ θ r,
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ 2 =
        (θ.1 * r ^ (3 : ℕ)) • Q θ r := by
    exact centerResidual_factorization_of_zeroRadius_and_punctured
      certificate.scale_zero certificate.punctured_factorization
  have hkernel : ∃ δ > 0,
      ContinuousOn
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ certificate.kernel z.1 z.2)
        (parameterSet β B ×ˢ Set.Icc (-δ) δ) ∧
      (∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ → Q θ r = certificate.kernel θ r) := by
    refine ⟨certificate.radius, certificate.radius_pos, certificate.kernel_continuous, ?_⟩
    exact certificate.quotient_eq_kernel
  have hquotient := exists_local_uniform_quotient_bound_of_continuousKernel
    β B Q certificate.kernel hkernel
  exact centerResidual_uniformBound_of_cubicFactorization hfactor hquotient

/-- Infrastructure for Appendix Lemma A.6: the same certificate exposes the
factorization independently, for callers that need to transport the quotient
before taking compact bounds. -/
theorem CenterResidualSourceCertificate.factorization
    {β B : ℝ} {Q : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (certificate : CenterResidualSourceCertificate β B Q) :
    ∀ θ r,
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ 2 =
        (θ.1 * r ^ (3 : ℕ)) • Q θ r := by
  exact centerResidual_factorization_of_zeroRadius_and_punctured
    certificate.scale_zero certificate.punctured_factorization

end DFP.TwoLeg.Mixed
