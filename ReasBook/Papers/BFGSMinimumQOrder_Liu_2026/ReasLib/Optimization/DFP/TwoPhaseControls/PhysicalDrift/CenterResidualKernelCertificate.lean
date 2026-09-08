module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.BranchAssembly
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterQuotientPuncturedAdapter
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualAdapter
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualRawFrameBridge
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.BranchAssembly
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterQuotientPuncturedAdapter
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualAdapter
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualRawFrameBridge

public section

noncomputable section

open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
The denominator-cleared formulation is the natural source boundary for the physical
center residual.  It keeps the removable zero branches separate from the continuous
kernel calculation and lets the compact quotient adapter handle the final bound.
-/

/-- Helper for Appendix Lemma A.6: the mixed cubic weight used to clear the removable
    denominator in the center residual. -/
def physicalCenterCubicWeight (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  θ.1 * r ^ (3 : ℕ)

/-- Helper for Appendix Lemma A.6: the zero-filled quotient associated with a scalar
    residual and its mixed cubic weight. -/
def zeroFilledCubicQuotient
    (N : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  if physicalCenterCubicWeight θ r = 0 then 0
  else N θ r / physicalCenterCubicWeight θ r

/-- Helper for Appendix Lemma A.6: a denominator-cleared kernel certificate records the
    source identities needed before any compact quotient estimate is applied. -/
structure CenterResidualKernelCertificate (β B : ℝ) where
  kernel : (ℝ × ℝ × ℝ) → ℝ → ℝ
  radius : ℝ
  radius_pos : 0 < radius
  scale_zero : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0
  punctured_factorization : ∀ θ r, θ.1 ≠ 0 → r ≠ 0 →
    physicalCenterResidual θ r =
      physicalCenterCubicWeight θ r • kernel θ r
  kernel_continuous : ContinuousOn
    (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ kernel z.1 z.2)
    (parameterSet β B ×ˢ Set.Icc (-radius) radius)

/-- Helper for Appendix Lemma A.6: vanishing of the mixed cubic weight forces the
    physical center residual to vanish under the two removable-branch certificates. -/
theorem CenterResidualKernelCertificate.residual_zero_of_weight_zero
    {β B : ℝ} (certificate : CenterResidualKernelCertificate β B)
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hweight : physicalCenterCubicWeight θ r = 0) :
    physicalCenterResidual θ r = 0 := by
  have hweight' : θ.1 * r ^ (3 : ℕ) = 0 := by
    simpa only [physicalCenterCubicWeight] using hweight
  rcases mul_eq_zero.mp hweight' with hθ | hrpow
  · exact certificate.scale_zero θ r hθ
  · have hr : r = 0 := by
      by_contra hr_ne
      exact (pow_ne_zero 3 hr_ne) hrpow
    rw [hr]
    simpa only [physicalCenterResidual] using centerResidual_zeroRadius θ

/-- Helper for Appendix Lemma A.6: the zero-filled cubic quotient of a kernel-certified
    residual has the prescribed denominator-cleared factorization on every branch. -/
theorem CenterResidualKernelCertificate.factorization
    {β B : ℝ} (certificate : CenterResidualKernelCertificate β B) :
    ∀ θ r,
      physicalCenterResidual θ r =
        physicalCenterCubicWeight θ r •
          zeroFilledCubicQuotient physicalCenterResidual θ r := by
  intro θ r
  by_cases hweight : physicalCenterCubicWeight θ r = 0
  · rw [certificate.residual_zero_of_weight_zero θ r hweight]
    simp only [zeroFilledCubicQuotient, hweight, if_pos, smul_zero]
  · simp only [zeroFilledCubicQuotient, hweight, if_false, smul_eq_mul]
    exact (mul_div_cancel₀ (physicalCenterResidual θ r) hweight).symm

/-- Appendix Lemma A.6 companion: a denominator-cleared continuous kernel certificate yields
    the uniform mixed-variable cubic bound for the physical center residual. -/
theorem CenterResidualKernelCertificate.uniformBound
    {β B : ℝ} (certificate : CenterResidualKernelCertificate β B) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
      ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ 2‖ ≤
      C * |θ.1| * |r| ^ (3 : ℝ) := by
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
    refine ⟨certificate.radius, certificate.radius_pos, certificate.kernel_continuous, ?_⟩
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
    simp only [smul_eq_mul]
    field_simp [hweight]
  obtain ⟨C, hC, δ, hδ, hQ⟩ :=
    exists_local_uniform_quotient_bound_of_continuousKernel_on_punctured
      β B Q certificate.kernel hkernel hzero
  have hfactor : ∀ θ r,
      physicalCenterResidual θ r =
        (physicalCenterCubicWeight θ r) • Q θ r := by
    intro θ r
    exact certificate.factorization θ r
  have hbound := centerResidual_uniformBound_of_cubicFactorization
    (K := parameterSet β B) (Q := Q) hfactor ⟨C, hC, δ, hδ, hQ⟩
  simpa only [physicalCenterResidual, physicalCenterCubicWeight] using hbound

end DFP.TwoLeg.Mixed
