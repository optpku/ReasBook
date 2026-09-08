module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawFrameCertificateAdapter
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawFrameCertificateAdapter

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
This module is the branch-level source interface for the physical center residual.
It deliberately keeps the frame comparison, displacement identities, and bracket
normal form as hypotheses.  The reusable part is the transport through the raw
certificate and the subsequent denominator-cleared cubic algebra.
-/

/-- Infrastructure I.16a: a raw bracket certificate transports the complete physical
    center displacement, before projecting to a single coordinate. -/
theorem CenterRaw.BracketCertificate.fullCenterDisplacement_eq_mul_bracket
    {b r : ℝ} {state : ℝ × ℝ × ℝ}
    (certificate : CenterRaw.BracketCertificate b r state) :
    (observableMap b state).fullCenterDisplacement =
      (b * r) • certificate.bracket := by
  let H₀ := CenterRaw.initialMetric state
  let g₀ := CenterRaw.initialGradient state
  let F := CenterRaw.firstFrame b state
  let H₁ := CenterRaw.secondMetric b state
  let firstStep := CenterRaw.firstStep b state
  let secondStep := CenterRaw.secondStep b state
  have hobs := observableMap_fullCenterDisplacement_eq_rawSteps b state
  have hfirst :
      (rawObservableStep H₀ g₀ (TwoPhaseControls.first b)).2.2 =
        r • certificate.firstNormalized := by
    simpa [CenterRaw.firstStep, CenterRaw.initialMetric, CenterRaw.initialGradient,
      H₀, g₀, firstStep] using certificate.first_displacement
  have hsecond :
      (rawObservableStep H₁
        (Matrix.mulVec F.transpose (rawObservableStep H₀ g₀
          (TwoPhaseControls.first b)).2.1)
        (TwoPhaseControls.second b)).2.2 =
        r • certificate.secondNormalized := by
    simpa [CenterRaw.secondStep, CenterRaw.secondMetric, CenterRaw.secondGradient,
      CenterRaw.firstStep, CenterRaw.initialMetric, CenterRaw.initialGradient,
      H₀, g₀, F, H₁, firstStep, secondStep] using certificate.second_displacement
  have hraw := rawObservableStep_centerDisplacement_eq_scaledBracket
    b r F H₀ H₁ g₀ certificate.firstNormalized certificate.secondNormalized
    certificate.frame_orthogonal hfirst hsecond
  simpa [CenterRaw.BracketCertificate.bracket, CenterRaw.firstFrame,
    CenterRaw.secondMetric, CenterRaw.secondGradient, CenterRaw.firstStep,
    CenterRaw.secondStep, CenterRaw.initialMetric, CenterRaw.initialGradient,
    H₀, g₀, F, H₁, firstStep, secondStep] using hobs.trans hraw

/-- Infrastructure I.16a: a pointwise signed raw-frame branch transports an arbitrary
    weighted bracket value to the corresponding physical center-residual factorization. -/
theorem centerResidual_eq_controlRadius_mul_bracketResidual_of_signedData
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    {F : Matrix (Fin 2) (Fin 2) ℝ}
    {u₀ u₁ : Fin 2 → ℝ} {W : ℝ}
    (horth : F * F.transpose = 1)
    (hbranch :
      (CenterRaw.firstFrame θ.1 (input θ r) = F ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 = r • u₁) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -F ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 = r • (-u₁)))
    (hfirst :
      (CenterRaw.firstStep θ.1 (input θ r)).2.2 = r • u₀)
    (hbracket : (weightedCenterBracket F u₀ u₁) 0 = W) :
    physicalCenterResidual θ r =
      (θ.1 * r) * (W - centerBracketCoefficient θ * r) := by
  obtain ⟨certificate, hcertificate⟩ :=
    CenterRaw.bracketCertificate_of_signedFrameData
      (F := F) (u₀ := u₀) (u₁ := u₁) (W := W)
      horth hbranch hfirst hbracket
  have hres := certificate.centerResidual_eq_controlRadius_mul_bracketResidual
  rw [hcertificate] at hres
  simpa only [physicalCenterResidual] using hres

/-- Infrastructure I.16a: zero-scale, zero-radius, and signed punctured branches
    assemble one unconditional center-residual bracket factorization on a radius tube. -/
theorem centerResidual_eq_controlRadius_mul_bracketResidual_of_branchData
    {K : Set (ℝ × ℝ × ℝ)}
    {W : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {F : (ℝ × ℝ × ℝ) → ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {u₀ u₁ : (ℝ × ℝ × ℝ) → ℝ → Fin 2 → ℝ}
    {δ : ℝ}
    (hscale : ∀ θ, θ ∈ K → ∀ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hradius : ∀ θ, θ ∈ K → physicalCenterResidual θ 0 = 0)
    (horth : ∀ θ, θ ∈ K → ∀ r, |r| < δ →
      F θ r * (F θ r).transpose = 1)
    (hbranch : ∀ θ, θ ∈ K → ∀ r, |r| < δ →
      (CenterRaw.firstFrame θ.1 (input θ r) = F θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 = r • u₁ θ r) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -F θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 = r • (-(u₁ θ r))))
    (hfirst : ∀ θ, θ ∈ K → ∀ r, |r| < δ →
      (CenterRaw.firstStep θ.1 (input θ r)).2.2 = r • u₀ θ r)
    (hbracket : ∀ θ, θ ∈ K → ∀ r, |r| < δ →
      (weightedCenterBracket (F θ r) (u₀ θ r) (u₁ θ r)) 0 = W θ r) :
    ∀ θ, θ ∈ K → ∀ r, |r| < δ →
      physicalCenterResidual θ r =
        (θ.1 * r) * (W θ r - centerBracketCoefficient θ * r) := by
  intro θ hθ r hr
  by_cases hθzero : θ.1 = 0
  · rw [hscale θ hθ r hθzero, hθzero]
    simp
  · by_cases hrzero : r = 0
    · subst r
      rw [hradius θ hθ]
      simp
    · exact centerResidual_eq_controlRadius_mul_bracketResidual_of_signedData
        (horth θ hθ r hr) (hbranch θ hθ r hr) (hfirst θ hθ r hr)
        (hbracket θ hθ r hr)

/-- Infrastructure I.16a: a branch-level bracket factorization and a quadratic kernel
    identity produce the denominator-cleared cubic center-residual transport. -/
theorem centerResidual_eq_cubicKernel_of_branchData
    {K : Set (ℝ × ℝ × ℝ)}
    {W : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {F : (ℝ × ℝ × ℝ) → ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {u₀ u₁ : (ℝ × ℝ × ℝ) → ℝ → Fin 2 → ℝ}
    {Q : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {δ : ℝ}
    (hscale : ∀ θ, θ ∈ K → ∀ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hradius : ∀ θ, θ ∈ K → physicalCenterResidual θ 0 = 0)
    (horth : ∀ θ, θ ∈ K → ∀ r, |r| < δ →
      F θ r * (F θ r).transpose = 1)
    (hbranch : ∀ θ, θ ∈ K → ∀ r, |r| < δ →
      (CenterRaw.firstFrame θ.1 (input θ r) = F θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 = r • u₁ θ r) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -F θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 = r • (-(u₁ θ r))))
    (hfirst : ∀ θ, θ ∈ K → ∀ r, |r| < δ →
      (CenterRaw.firstStep θ.1 (input θ r)).2.2 = r • u₀ θ r)
    (hbracket : ∀ θ, θ ∈ K → ∀ r, |r| < δ →
      (weightedCenterBracket (F θ r) (u₀ θ r) (u₁ θ r)) 0 = W θ r)
    (hkernel : ∀ θ, θ ∈ K → ∀ r, |r| < δ →
      W θ r - centerBracketCoefficient θ * r = r ^ 2 * Q θ r) :
    ∀ θ, θ ∈ K → ∀ r, |r| < δ →
      physicalCenterResidual θ r = (θ.1 * r ^ 3) • Q θ r := by
  intro θ hθ r hr
  have hbracket := centerResidual_eq_controlRadius_mul_bracketResidual_of_branchData
    (W := W) (F := F) (u₀ := u₀) (u₁ := u₁) hscale hradius horth hbranch hfirst hbracket
  rw [hbracket θ hθ r hr, hkernel θ hθ r hr]
  simp only [smul_eq_mul]
  ring

end DFP.TwoLeg.Mixed
