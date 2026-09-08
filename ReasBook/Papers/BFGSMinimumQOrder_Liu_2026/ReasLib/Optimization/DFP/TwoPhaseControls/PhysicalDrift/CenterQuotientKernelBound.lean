module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualKernelCertificate
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualKernelCertificate

public section

noncomputable section

open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
This companion is the source-facing quotient-bound adapter for the physical center
residual.  A `CenterResidualKernelCertificate` supplies the removable branches and
the continuous denominator-cleared kernel; the theorem below exposes the resulting
bound in the exact zero-filled quotient shape used by the parent residual proof.
-/

/-- Helper for PhysicalDrift / Appendix Lemma A.6: a denominator-cleared center
    kernel certificate gives a local uniform bound for the parent zero-filled
    quotient `residual / (θ.1 * r ^ 3)`. -/
theorem CenterResidualKernelCertificate.zeroFilledCubicQuotient_uniformBound
    {β B : ℝ} (certificate : CenterResidualKernelCertificate β B) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
      ‖(if θ.1 * r ^ (3 : ℕ) = 0 then 0 else
        ((observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ 2) / (θ.1 * r ^ (3 : ℕ)))‖ ≤ C := by
  let Q : (ℝ × ℝ × ℝ) → ℝ → ℝ :=
    zeroFilledCubicQuotient physicalCenterResidual
  have hzero : ∀ θ r, physicalCenterCubicWeight θ r = 0 → Q θ r = 0 := by
    intro θ r hweight
    simp only [Q, zeroFilledCubicQuotient, hweight, if_pos]
  have hkernel : ∃ δ > 0,
      ContinuousOn
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ certificate.kernel z.1 z.2)
        (parameterSet β B ×ˢ Set.Icc (-δ) δ) ∧
      (∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
        physicalCenterCubicWeight θ r ≠ 0 → Q θ r = certificate.kernel θ r) := by
    refine ⟨certificate.radius, certificate.radius_pos,
      certificate.kernel_continuous, ?_⟩
    intro θ hθ r hr hweight
    have hθ' : θ.1 ≠ 0 := by
      intro hθzero
      apply hweight
      simp [physicalCenterCubicWeight, hθzero]
    have hr' : r ≠ 0 := by
      intro hrzero
      apply hweight
      simp [physicalCenterCubicWeight, hrzero]
    have hpunctured := certificate.punctured_factorization θ r hθ' hr'
    simp only [Q, zeroFilledCubicQuotient, hweight, if_false]
    rw [hpunctured]
    simp only [physicalCenterCubicWeight, smul_eq_mul]
    field_simp [hweight]
  obtain ⟨C, hC, δ, hδ, hQ⟩ :=
    exists_local_uniform_quotient_bound_of_continuousKernel_on_punctured
      β B Q certificate.kernel hkernel hzero
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro θ hθ r hr
  have hbound := hQ θ hθ r hr
  simpa only [Q, zeroFilledCubicQuotient, physicalCenterResidual,
    physicalCenterCubicWeight] using hbound

end DFP.TwoLeg.Mixed
