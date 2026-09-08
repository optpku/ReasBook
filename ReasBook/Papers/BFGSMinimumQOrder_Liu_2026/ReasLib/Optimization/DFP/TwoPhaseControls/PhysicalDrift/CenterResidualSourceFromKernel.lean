module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualKernelCertificate
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualSourceCertificate
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualKernelCertificate
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualSourceCertificate

public section

noncomputable section

open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
This adapter is the source-facing boundary between a denominator-cleared kernel and
the quotient certificate consumed by the physical-drift assembly.  At a removable
branch the quotient keeps the continuous kernel value, while on the punctured branch
it is the exact residual quotient.
-/

/-- Helper for Infrastructure I.16a: fill the removable branches of a kernel quotient with
the kernel value, and use the exact denominator quotient elsewhere. -/
def kernelFilledCubicQuotient
    {β B : ℝ} (certificate : CenterResidualKernelCertificate β B)
    (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  if physicalCenterCubicWeight θ r = 0 then
    certificate.kernel θ r
  else
    physicalCenterResidual θ r / physicalCenterCubicWeight θ r

/-- Helper for Infrastructure I.16a: the filled quotient agrees with the kernel on a zero
weight branch, including the zero-radius and zero-scale cases. -/
theorem kernelFilledCubicQuotient_eq_kernel_of_weight_zero
    {β B : ℝ} (certificate : CenterResidualKernelCertificate β B)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hweight : physicalCenterCubicWeight θ r = 0) :
    kernelFilledCubicQuotient certificate θ r = certificate.kernel θ r := by
  simp only [kernelFilledCubicQuotient, hweight, if_pos]

/-- Helper for Infrastructure I.16a: on a nonzero mixed cubic branch, the filled quotient is
the exact residual divided by its denominator. -/
theorem kernelFilledCubicQuotient_eq_residual_div_of_weight_ne_zero
    {β B : ℝ} (certificate : CenterResidualKernelCertificate β B)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hweight : physicalCenterCubicWeight θ r ≠ 0) :
    kernelFilledCubicQuotient certificate θ r =
      physicalCenterResidual θ r / physicalCenterCubicWeight θ r := by
  simp only [kernelFilledCubicQuotient, hweight, if_false]

/-- Helper for Infrastructure I.16a: the kernel certificate supplies the source residual's
zero-scale branch in the notation used by `CenterResidualSourceCertificate`. -/
theorem CenterResidualKernelCertificate.source_scale_zero
    {β B : ℝ} (certificate : CenterResidualKernelCertificate β B) :
    ∀ θ r, θ.1 = 0 →
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ 2 = 0 := by
  intro θ r hθ
  simpa only [physicalCenterResidual] using certificate.scale_zero θ r hθ

/-- Helper for Infrastructure I.16a: on a punctured branch the filled quotient reconstructs
the denominator-cleared residual exactly. -/
theorem CenterResidualKernelCertificate.source_punctured_factorization
    {β B : ℝ} (certificate : CenterResidualKernelCertificate β B) :
    ∀ θ r, θ.1 ≠ 0 → r ≠ 0 →
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ 2 =
        (θ.1 * r ^ (3 : ℕ)) • kernelFilledCubicQuotient certificate θ r := by
  intro θ r hθ hr
  have hweight : physicalCenterCubicWeight θ r ≠ 0 := by
    simp only [physicalCenterCubicWeight]
    exact mul_ne_zero hθ (pow_ne_zero 3 hr)
  have hfactor := certificate.punctured_factorization θ r hθ hr
  have hsource : physicalCenterResidual θ r =
      physicalCenterCubicWeight θ r • kernelFilledCubicQuotient certificate θ r := by
    calc
      physicalCenterResidual θ r =
          physicalCenterCubicWeight θ r • certificate.kernel θ r := hfactor
      _ = physicalCenterCubicWeight θ r •
          (physicalCenterResidual θ r / physicalCenterCubicWeight θ r) := by
        rw [hfactor]
        simp only [smul_eq_mul]
        field_simp [hweight]
      _ = physicalCenterCubicWeight θ r •
          kernelFilledCubicQuotient certificate θ r := by
        rw [kernelFilledCubicQuotient_eq_residual_div_of_weight_ne_zero
          certificate hweight]
  simpa only [physicalCenterResidual, physicalCenterCubicWeight] using hsource

/-- Helper for Infrastructure I.16a: the filled quotient agrees with the continuous kernel on
the whole source tube, including removable branches. -/
theorem CenterResidualKernelCertificate.source_quotient_eq_kernel
    {β B : ℝ} (certificate : CenterResidualKernelCertificate β B) :
    ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < certificate.radius →
      kernelFilledCubicQuotient certificate θ r = certificate.kernel θ r := by
  intro θ hθ r hr
  by_cases hweight : physicalCenterCubicWeight θ r = 0
  · exact kernelFilledCubicQuotient_eq_kernel_of_weight_zero certificate hweight
  · have hθne : θ.1 ≠ 0 := by
      intro hθzero
      apply hweight
      rw [physicalCenterCubicWeight, hθzero]
      simp
    have hrne : r ≠ 0 := by
      intro hrzero
      apply hweight
      rw [physicalCenterCubicWeight, hrzero]
      simp
    have hfactor := certificate.punctured_factorization θ r hθne hrne
    rw [kernelFilledCubicQuotient_eq_residual_div_of_weight_ne_zero
      certificate hweight, hfactor]
    simp only [smul_eq_mul]
    field_simp [hweight]

/-- Infrastructure I.16a: a denominator-cleared continuous kernel certificate produces the
source-facing quotient certificate without imposing a value on removable branches. -/
noncomputable def CenterResidualKernelCertificate.toSourceCertificate
    {β B : ℝ} (certificate : CenterResidualKernelCertificate β B) :
    CenterResidualSourceCertificate β B
      (kernelFilledCubicQuotient certificate) :=
  { kernel := certificate.kernel
    radius := certificate.radius
    radius_pos := certificate.radius_pos
    scale_zero := certificate.source_scale_zero
    punctured_factorization := certificate.source_punctured_factorization
    kernel_continuous := certificate.kernel_continuous
    quotient_eq_kernel := certificate.source_quotient_eq_kernel }

end DFP.TwoLeg.Mixed
