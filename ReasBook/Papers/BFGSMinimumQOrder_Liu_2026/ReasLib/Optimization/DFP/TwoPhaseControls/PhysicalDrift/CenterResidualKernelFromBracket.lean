module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualKernelCertificate
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawFrameCertificateAdapter
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualKernelCertificate
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawFrameCertificateAdapter
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketTransport

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
This companion is the source-facing constructor from a raw-frame bracket identity
to the denominator-cleared center-residual certificate.  It keeps the evaluator
hidden behind `CenterRaw.BracketCertificate.centerResidual_eq_cubicKernel` and
leaves the source-specific bracket calculation as the sole hypothesis.
-/

/-- Helper for Infrastructure I.16a: a raw bracket kernel identity gives the
    punctured denominator-cleared residual factorization. -/
theorem centerResidual_factorization_of_rawBracketKernel
    (K : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (hbracket : ∀ θ r, θ.1 ≠ 0 → r ≠ 0 →
      ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
        certificate.bracket 0 - centerBracketCoefficient θ * r = r ^ 2 * K θ r)
    : ∀ θ r, θ.1 ≠ 0 → r ≠ 0 →
      physicalCenterResidual θ r =
        physicalCenterCubicWeight θ r • K θ r := by
  intro θ r hθ hr
  obtain ⟨certificate, hkernel⟩ := hbracket θ r hθ hr
  exact certificate.centerResidual_eq_cubicKernel hkernel

/-- Infrastructure I.16a: a scale-zero certificate restricted to a set gives the
    zero-filled cubic factorization on that set, including the universal radius-zero
    branch. -/
theorem centerResidual_eq_cubicWeight_smul_zeroFilledQuotient_on
    (S : Set (ℝ × ℝ × ℝ))
    (hscale : ∀ θ ∈ S, ∀ r, θ.1 = 0 → physicalCenterResidual θ r = 0) :
    ∀ θ ∈ S, ∀ r,
      physicalCenterResidual θ r =
        physicalCenterCubicWeight θ r •
          centerBracketZeroFilledQuotient physicalCenterResidual θ r := by
  intro θ hθS r
  by_cases hweight : physicalCenterCubicWeight θ r = 0
  · have hweight' : θ.1 * r ^ (3 : ℕ) = 0 := by
      simpa only [physicalCenterCubicWeight] using hweight
    have hres : physicalCenterResidual θ r = 0 := by
      rcases mul_eq_zero.mp hweight' with hθ | hrpow
      · exact hscale θ hθS r hθ
      · have hr : r = 0 := by
          exact eq_zero_of_pow_eq_zero hrpow
        rw [hr]
        change
          (observableMap θ.1 (input θ 0)).fullCenterDisplacement 0 -
              centerDriftCoefficient θ * 0 ^ (2 : ℕ) = 0
        exact centerResidual_zeroRadius θ
    have hquot_zero :
        centerBracketZeroFilledQuotient physicalCenterResidual θ r = 0 := by
      simp only [centerBracketZeroFilledQuotient, hweight', if_pos]
    rw [hres, hquot_zero]
    simp [hweight]
  · have hweight' : θ.1 * r ^ (3 : ℕ) ≠ 0 := by
      intro hzero
      apply hweight
      simpa only [physicalCenterCubicWeight] using hzero
    have hquot :
        centerBracketZeroFilledQuotient physicalCenterResidual θ r =
          physicalCenterResidual θ r / (θ.1 * r ^ (3 : ℕ)) := by
      simp only [centerBracketZeroFilledQuotient, hweight', if_false]
    rw [hquot, smul_eq_mul]
    exact (mul_div_cancel₀ (physicalCenterResidual θ r) hweight').symm

/-- Helper for Infrastructure I.16a: a global scale-zero certificate is the
    unrestricted specialization of the set-indexed zero-filled factorization. -/
theorem centerResidual_eq_cubicWeight_smul_zeroFilledQuotient_of_scaleZero
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0) :
    ∀ θ r,
      physicalCenterResidual θ r =
        physicalCenterCubicWeight θ r •
          centerBracketZeroFilledQuotient physicalCenterResidual θ r := by
  intro θ r
  exact centerResidual_eq_cubicWeight_smul_zeroFilledQuotient_on
    Set.univ (fun η _ s hη ↦ hscale η s hη) θ (Set.mem_univ θ) r

/-- Infrastructure I.16a: an existential raw bracket certificate on the punctured
    branch, together with removable-branch coverage, transports a quadratic bracket
    remainder to the full denominator-cleared center residual. -/
theorem centerResidual_eq_cubicKernel_of_bracketCertificateCover
    {K W : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {P : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (hscale : ∀ θ r, P θ r → θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ r, P θ r →
      θ.1 = 0 ∨ r = 0 ∨
        ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
          certificate.bracket 0 = W θ r)
    (hkernel : ∀ θ r, P θ r → θ.1 ≠ 0 → r ≠ 0 →
      W θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r)
    {θ : ℝ × ℝ × ℝ} {r : ℝ} (hP : P θ r) :
    physicalCenterResidual θ r = physicalCenterCubicWeight θ r • K θ r := by
  by_cases hθ : θ.1 = 0
  · have hres := hscale θ r hP hθ
    have hweight : physicalCenterCubicWeight θ r = 0 := by
      simp only [physicalCenterCubicWeight, hθ, zero_mul]
    rw [hres, hweight, zero_smul]
  · by_cases hr : r = 0
    · subst r
      have hres : physicalCenterResidual θ 0 = 0 := by
        simpa only [physicalCenterResidual] using centerResidual_zeroRadius θ
      rw [hres]
      simp [physicalCenterCubicWeight]
    · rcases hcover θ r hP with hθzero | hrzero | hcertificate
      · exact (hθ hθzero).elim
      · exact (hr hrzero).elim
      · obtain ⟨certificate, hbracket⟩ := hcertificate
        have hkernel' : certificate.bracket 0 - centerBracketCoefficient θ * r =
            r ^ 2 * K θ r := by
          rw [hbracket]
          exact hkernel θ r hP hθ hr
        exact certificate.centerResidual_eq_cubicKernel hkernel'

/-- Infrastructure I.16a: the same bracket-cover interface gives the raw evaluator's
    coordinate-zero displacement as the prescribed quadratic drift plus its cubic kernel. -/
theorem fullCenterDisplacement_coord_zero_eq_drift_add_cubicKernel_of_bracketCertificateCover
    {K W : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {P : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (hscale : ∀ θ r, P θ r → θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ r, P θ r →
      θ.1 = 0 ∨ r = 0 ∨
        ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
          certificate.bracket 0 = W θ r)
    (hkernel : ∀ θ r, P θ r → θ.1 ≠ 0 → r ≠ 0 →
      W θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r)
    {θ : ℝ × ℝ × ℝ} {r : ℝ} (hP : P θ r) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 =
      centerDriftCoefficient θ * r ^ 2 +
        physicalCenterCubicWeight θ r • K θ r := by
  have hres := centerResidual_eq_cubicKernel_of_bracketCertificateCover
    hscale hcover hkernel hP
  unfold physicalCenterResidual at hres
  linarith

/-- Helper for Infrastructure I.16a: signed raw-frame data and a canonical
    bracket remainder produce the raw `BracketCertificate` consumed by the
    denominator-cleared kernel interface. -/
theorem CenterRaw.bracketKernelCertificate_of_signedFrameData
    {θ : ℝ × ℝ × ℝ} {r K : ℝ}
    (horth :
      canonicalFirstFrame θ r * (canonicalFirstFrame θ r).transpose = 1)
    (hbranch :
      (CenterRaw.firstFrame θ.1 (input θ r) = canonicalFirstFrame θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • canonicalSecondNormalizedDisplacement θ r) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -canonicalFirstFrame θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • (-canonicalSecondNormalizedDisplacement θ r)))
    (hfirst :
      (CenterRaw.firstStep θ.1 (input θ r)).2.2 =
        r • canonicalFirstNormalizedDisplacement θ r)
    (hkernel :
      canonicalCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K) :
    ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
      certificate.bracket 0 - centerBracketCoefficient θ * r = r ^ 2 * K := by
  have hbracket :
      (weightedCenterBracket (canonicalFirstFrame θ r)
        (canonicalFirstNormalizedDisplacement θ r)
        (canonicalSecondNormalizedDisplacement θ r)) 0 =
        canonicalCenterBracket θ r := by
    rfl
  obtain ⟨certificate, hcertificate⟩ :=
    CenterRaw.bracketCertificate_of_signedFrameData
      (F := canonicalFirstFrame θ r)
      (u₀ := canonicalFirstNormalizedDisplacement θ r)
      (u₁ := canonicalSecondNormalizedDisplacement θ r)
      (W := canonicalCenterBracket θ r)
      horth hbranch hfirst hbracket
  refine ⟨certificate, ?_⟩
  rw [hcertificate]
  exact hkernel

/-- Helper for Infrastructure I.16a: signed raw-frame data and a canonical
    quadratic bracket remainder give the physical cubic-kernel identity. -/
theorem centerResidual_eq_cubicKernel_of_signedFrameData
    {θ : ℝ × ℝ × ℝ} {r K : ℝ}
    (horth :
      canonicalFirstFrame θ r * (canonicalFirstFrame θ r).transpose = 1)
    (hbranch :
      (CenterRaw.firstFrame θ.1 (input θ r) = canonicalFirstFrame θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • canonicalSecondNormalizedDisplacement θ r) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -canonicalFirstFrame θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • (-canonicalSecondNormalizedDisplacement θ r)))
    (hfirst :
      (CenterRaw.firstStep θ.1 (input θ r)).2.2 =
        r • canonicalFirstNormalizedDisplacement θ r)
    (hkernel :
      canonicalCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K) :
    physicalCenterResidual θ r = physicalCenterCubicWeight θ r • K := by
  obtain ⟨certificate, hbracket⟩ :=
    CenterRaw.bracketKernelCertificate_of_signedFrameData
      horth hbranch hfirst hkernel
  exact certificate.centerResidual_eq_cubicKernel hbracket

/-- Infrastructure I.16a: signed raw-frame data expose the full evaluator's coordinate-zero
    displacement directly in the canonical weighted-bracket coordinates. -/
theorem CenterRaw.fullCenterDisplacement_coord_zero_eq_canonicalBracket_of_signedFrameData
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (horth :
      canonicalFirstFrame θ r * (canonicalFirstFrame θ r).transpose = 1)
    (hbranch :
      (CenterRaw.firstFrame θ.1 (input θ r) = canonicalFirstFrame θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • canonicalSecondNormalizedDisplacement θ r) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -canonicalFirstFrame θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • (-canonicalSecondNormalizedDisplacement θ r)))
    (hfirst :
      (CenterRaw.firstStep θ.1 (input θ r)).2.2 =
        r • canonicalFirstNormalizedDisplacement θ r) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 =
      (θ.1 * r) * canonicalCenterBracket θ r := by
  have hbracket :
      (weightedCenterBracket (canonicalFirstFrame θ r)
        (canonicalFirstNormalizedDisplacement θ r)
        (canonicalSecondNormalizedDisplacement θ r)) 0 =
        canonicalCenterBracket θ r := by
    rfl
  obtain ⟨certificate, hcertificate⟩ :=
    CenterRaw.bracketCertificate_of_signedFrameData
      (F := canonicalFirstFrame θ r)
      (u₀ := canonicalFirstNormalizedDisplacement θ r)
      (u₁ := canonicalSecondNormalizedDisplacement θ r)
      (W := canonicalCenterBracket θ r)
      horth hbranch hfirst hbracket
  have hraw := certificate.fullCenterDisplacement_coord_zero_eq_mul_bracket
  rw [hcertificate] at hraw
  exact hraw

/-- Infrastructure I.16a: a global raw bracket kernel identity assembles the
    corresponding denominator-cleared center-residual certificate. -/
def CenterResidualKernelCertificate.of_rawBracketKernel
    {β B : ℝ}
    (K : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (radius : ℝ)
    (hradius : 0 < radius)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hbracket : ∀ θ r, θ.1 ≠ 0 → r ≠ 0 →
      ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
        certificate.bracket 0 - centerBracketCoefficient θ * r = r ^ 2 * K θ r)
    (hK : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-radius) radius)) :
    CenterResidualKernelCertificate β B :=
  { kernel := K
    radius := radius
    radius_pos := hradius
    scale_zero := hscale
    punctured_factorization :=
      centerResidual_factorization_of_rawBracketKernel K hbracket
    kernel_continuous := hK }

/- The canonical-frame constructor is kept next to the raw constructor so callers
   can choose either the already packaged bracket certificate or the source-facing
   frame/displacement data without rebuilding the intermediate existential. -/

/-- Helper for Infrastructure I.16a: a frame-kernel specification names the frame,
    two normalized displacement paths, and scalar bracket normal form independently
    of any particular source evaluator. -/
structure FrameKernelSpec : Type where
  frame : (ℝ × ℝ × ℝ) → ℝ → Matrix (Fin 2) (Fin 2) ℝ
  first : (ℝ × ℝ × ℝ) → ℝ → Fin 2 → ℝ
  second : (ℝ × ℝ × ℝ) → ℝ → Fin 2 → ℝ
  bracket : (ℝ × ℝ × ℝ) → ℝ → ℝ

/-- Helper for Infrastructure I.16a: a domain-indexed frame-kernel certificate records
    the source compatibility data only on the predicate `D`. -/
structure FrameKernelDataOn
    (spec : FrameKernelSpec)
    (K : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (D : (ℝ × ℝ × ℝ) → ℝ → Prop) : Prop where
  orthogonal : ∀ θ r, D θ r →
    spec.frame θ r * (spec.frame θ r).transpose = 1
  branch : ∀ θ r, D θ r →
    (CenterRaw.firstFrame θ.1 (input θ r) = spec.frame θ r ∧
      (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
        r • spec.second θ r) ∨
    (CenterRaw.firstFrame θ.1 (input θ r) = -spec.frame θ r ∧
      (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
        r • (-spec.second θ r))
  firstDisplacement : ∀ θ r, D θ r →
    (CenterRaw.firstStep θ.1 (input θ r)).2.2 = r • spec.first θ r
  bracketValue : ∀ θ r, D θ r →
    (weightedCenterBracket (spec.frame θ r) (spec.first θ r) (spec.second θ r)) 0 =
      spec.bracket θ r
  bracketKernel : ∀ θ r, D θ r →
    spec.bracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r

/-- Helper for Infrastructure I.16a: the canonical frame specification specializes the
    generic frame-kernel package to the mixed center bracket coordinates. -/
def canonicalFrameKernelSpec : FrameKernelSpec :=
  { frame := canonicalFirstFrame
    first := canonicalFirstNormalizedDisplacement
    second := canonicalSecondNormalizedDisplacement
    bracket := canonicalCenterBracket }

/-- Helper for Infrastructure I.16a: canonical frame data are a specialization of the
    domain-indexed generic frame-kernel certificate. -/
abbrev CanonicalFrameKernelDataOn
    (K : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (D : (ℝ × ℝ × ℝ) → ℝ → Prop) : Prop :=
  FrameKernelDataOn canonicalFrameKernelSpec K D

/-- Helper for Infrastructure I.16a: the standard punctured chart is a compatibility
    specialization of the domain-indexed canonical frame package. -/
abbrev CanonicalFrameKernelData (K : (ℝ × ℝ × ℝ) → ℝ → ℝ) :
    Prop :=
  CanonicalFrameKernelDataOn K (fun θ r ↦ θ.1 ≠ 0 ∧ r ≠ 0)

/-- Helper for Infrastructure I.16a: domain-indexed frame data expose a raw bracket
    certificate without strengthening the source chart domain to all punctured points. -/
theorem FrameKernelDataOn.bracketCertificate
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hD : D θ r) :
    ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
      certificate.bracket 0 = spec.bracket θ r := by
  have hbracket := data.bracketValue θ r hD
  exact CenterRaw.bracketCertificate_of_signedFrameData
    (F := spec.frame θ r) (u₀ := spec.first θ r) (u₁ := spec.second θ r)
    (W := spec.bracket θ r) (data.orthogonal θ r hD)
    (data.branch θ r hD) (data.firstDisplacement θ r hD) hbracket

/-- Infrastructure I.16a: a compact local frame domain and a radius tube cover
    assemble the pointwise raw certificates required by the existing bracket-germ
    quotient bound, while keeping the zero-radius certificate explicit. -/
theorem FrameKernelDataOn.zeroFilledQuotient_uniformBound_of_localCover
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    (S : Set (ℝ × ℝ × ℝ))
    (hS : IsCompact S)
    (hW : IndependentRadiusTruncatedGerm
      (fun θ r ↦ spec.bracket θ r) S 2
      (fun n θ ↦ (![0, centerBracketCoefficient θ] : Fin 2 → ℝ) n))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hcover : ∀ θ ∈ S, ∀ r : ℝ, |r| < δ₀ → r = 0 ∨ D θ r)
    (hzero : ∀ θ ∈ S,
      ∃ certificate : CenterRaw.BracketCertificate θ.1 0 (input θ 0),
        certificate.bracket 0 = spec.bracket θ 0) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ S, ∀ r : ℝ, |r| < δ →
      ‖centerBracketZeroFilledQuotient physicalCenterResidual θ r‖ ≤ C := by
  have hcertificate : ∀ θ ∈ S, ∀ r : ℝ, |r| < δ₀ →
      ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
        certificate.bracket 0 = spec.bracket θ r := by
    intro θ hθ r hr
    rcases hcover θ hθ r hr with hrzero | hD
    · subst r
      exact hzero θ hθ
    · exact data.bracketCertificate hD
  exact centerResidual_zeroFilledQuotient_uniformBound_of_bracketGerm
    (W := fun θ r ↦ spec.bracket θ r) hS hW δ₀ hδ₀ hcertificate

/-- Helper for Infrastructure I.16a: a local frame-kernel cover yields the final
    mixed-variable residual estimate after the removable zero-weight branches are
    discharged explicitly. -/
theorem FrameKernelDataOn.uniformBound_of_localCover
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    (S : Set (ℝ × ℝ × ℝ))
    (hS : IsCompact S)
    (hW : IndependentRadiusTruncatedGerm
      (fun θ r ↦ spec.bracket θ r) S 2
      (fun n θ ↦ (![0, centerBracketCoefficient θ] : Fin 2 → ℝ) n))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ ∈ S, ∀ r : ℝ, |r| < δ₀ → r = 0 ∨ D θ r)
    (hzero : ∀ θ ∈ S,
      ∃ certificate : CenterRaw.BracketCertificate θ.1 0 (input θ 0),
        certificate.bracket 0 = spec.bracket θ 0) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ S, ∀ r : ℝ, |r| < δ →
      ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ (2 : ℕ)‖ ≤
      C * |θ.1| * |r| ^ (3 : ℝ) := by
  have hquotient := data.zeroFilledQuotient_uniformBound_of_localCover
    S hS hW δ₀ hδ₀ hcover hzero
  have hfactor :=
    centerResidual_eq_cubicWeight_smul_zeroFilledQuotient_of_scaleZero hscale
  have hfactor' : ∀ θ r,
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ (2 : ℕ) =
        (θ.1 * r ^ (3 : ℕ)) •
          centerBracketZeroFilledQuotient physicalCenterResidual θ r := by
    intro θ r
    simpa only [physicalCenterResidual, physicalCenterCubicWeight] using hfactor θ r
  exact centerResidual_uniformBound_of_cubicFactorization hfactor' hquotient

/-- Infrastructure I.16a: the compact local-cover estimate only needs the scale-zero
    certificate on the parameter set being bounded. -/
theorem FrameKernelDataOn.uniformBound_of_localCover_on
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    (S : Set (ℝ × ℝ × ℝ))
    (hS : IsCompact S)
    (hW : IndependentRadiusTruncatedGerm
      (fun θ r ↦ spec.bracket θ r) S 2
      (fun n θ ↦ (![0, centerBracketCoefficient θ] : Fin 2 → ℝ) n))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hscale : ∀ θ ∈ S, ∀ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ ∈ S, ∀ r : ℝ, |r| < δ₀ → r = 0 ∨ D θ r)
    (hzero : ∀ θ ∈ S,
      ∃ certificate : CenterRaw.BracketCertificate θ.1 0 (input θ 0),
        certificate.bracket 0 = spec.bracket θ 0) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ S, ∀ r : ℝ, |r| < δ →
      ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ (2 : ℕ)‖ ≤
      C * |θ.1| * |r| ^ (3 : ℝ) := by
  have hquotient := data.zeroFilledQuotient_uniformBound_of_localCover
    S hS hW δ₀ hδ₀ hcover hzero
  obtain ⟨C, hC, δ, hδ, hQ⟩ := hquotient
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro θ hθ r hr
  have hfactor := centerResidual_eq_cubicWeight_smul_zeroFilledQuotient_on
    S hscale θ hθ r
  have hfactor' :
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ (2 : ℕ) =
      (θ.1 * r ^ (3 : ℕ)) •
        centerBracketZeroFilledQuotient physicalCenterResidual θ r := by
    simpa only [physicalCenterResidual, physicalCenterCubicWeight] using hfactor
  rw [hfactor']
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow]
  have hnonneg : 0 ≤ |θ.1| * |r| ^ (3 : ℕ) := by positivity
  calc
    (|θ.1| * |r| ^ (3 : ℕ)) *
        ‖centerBracketZeroFilledQuotient physicalCenterResidual θ r‖ ≤
        (|θ.1| * |r| ^ (3 : ℕ)) * C :=
      mul_le_mul_of_nonneg_left (hQ θ hθ r hr) hnonneg
    _ = C * |θ.1| * |r| ^ (3 : ℕ) := by ring
    _ = C * |θ.1| * |r| ^ (3 : ℝ) := by
      have hpow : |r| ^ (3 : ℝ) = |r| ^ (3 : ℕ) := by
        norm_num [Real.rpow_natCast]
      rw [hpow]

/-- Infrastructure I.16a: a domain-indexed frame package exposes the raw evaluator's
    coordinate-zero center displacement in the supplied frame bracket coordinates. -/
theorem FrameKernelDataOn.fullCenterDisplacement_coord_zero_eq_specBracket
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hD : D θ r) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 =
      (θ.1 * r) * spec.bracket θ r := by
  obtain ⟨certificate, hbracket⟩ := data.bracketCertificate hD
  have hraw := certificate.fullCenterDisplacement_coord_zero_eq_mul_bracket
  rw [hbracket] at hraw
  exact hraw

/-- Infrastructure I.16a: removable scale and radius branches extend the raw evaluator
    bracket identity from a source domain to a predicate-covered region. -/
theorem FrameKernelDataOn.fullCenterDisplacement_coord_zero_eq_specBracket_of_cover
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D P : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    (hscale : ∀ θ r, P θ r → θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ r, P θ r →
      θ.1 = 0 ∨ r = 0 ∨ D θ r)
    {θ : ℝ × ℝ × ℝ} {r : ℝ} (hP : P θ r) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 =
      (θ.1 * r) * spec.bracket θ r := by
  rcases hcover θ r hP with hθ | hr | hD
  · have hres := hscale θ r hP hθ
    have hcoefficient : centerDriftCoefficient θ = 0 := by
      rw [centerDriftCoefficient_eq_control_mul_centerBracketCoefficient]
      simp [hθ]
    have heval :
        (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 = 0 := by
      simpa only [physicalCenterResidual, hcoefficient, zero_mul, sub_zero] using hres
    rw [heval, hθ]
    simp
  · have hres : physicalCenterResidual θ 0 = 0 := by
      simpa only [physicalCenterResidual] using centerResidual_zeroRadius θ
    have heval :
        (observableMap θ.1 (input θ 0)).fullCenterDisplacement 0 = 0 := by
      simpa [physicalCenterResidual] using hres
    rw [hr, heval]
    simp
  · exact data.fullCenterDisplacement_coord_zero_eq_specBracket hD

/-- Helper for Infrastructure I.16a: the same frame package expresses the physical residual as
    the control-radius factor times its supplied bracket remainder. -/
theorem FrameKernelDataOn.centerResidual_eq_controlRadius_mul_specBracketResidual
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hD : D θ r) :
    physicalCenterResidual θ r =
      (θ.1 * r) * (spec.bracket θ r - centerBracketCoefficient θ * r) := by
  have hraw := data.fullCenterDisplacement_coord_zero_eq_specBracket hD
  unfold physicalCenterResidual
  rw [hraw, centerDriftCoefficient_eq_control_mul_centerBracketCoefficient]
  ring

/-- Helper for Infrastructure I.16a: punctured canonical frame data expose the
    pointwise raw bracket certificate with its canonical bracket value. -/
theorem CanonicalFrameKernelData.bracketCertificate
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (data : CanonicalFrameKernelData K)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hθ : θ.1 ≠ 0) (hr : r ≠ 0) :
    ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
      certificate.bracket 0 = canonicalCenterBracket θ r := by
  have hD : θ.1 ≠ 0 ∧ r ≠ 0 := ⟨hθ, hr⟩
  exact FrameKernelDataOn.bracketCertificate data hD

/-- Helper for Infrastructure I.16a: canonical punctured frame data expose the raw evaluator's
    coordinate-zero displacement in canonical bracket coordinates. -/
theorem CanonicalFrameKernelData.fullCenterDisplacement_coord_zero_eq_canonicalBracket
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (data : CanonicalFrameKernelData K)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hθ : θ.1 ≠ 0) (hr : r ≠ 0) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 =
      (θ.1 * r) * canonicalCenterBracket θ r := by
  exact FrameKernelDataOn.fullCenterDisplacement_coord_zero_eq_specBracket data ⟨hθ, hr⟩

/-- Helper for Infrastructure I.16a: domain-indexed frame data transport a canonical
    quadratic bracket remainder to a denominator-cleared raw certificate. -/
theorem FrameKernelDataOn.bracketKernelCertificate
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hD : D θ r) :
    ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
      certificate.bracket 0 - centerBracketCoefficient θ * r = r ^ 2 * K θ r := by
  obtain ⟨certificate, hbracket⟩ := data.bracketCertificate hD
  refine ⟨certificate, ?_⟩
  rw [hbracket]
  exact data.bracketKernel θ r hD

/-- Helper for Infrastructure I.16a: the pointwise canonical bracket certificate
    already carries the denominator-cleared quadratic remainder. -/
theorem CanonicalFrameKernelData.bracketKernelCertificate
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (data : CanonicalFrameKernelData K)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hθ : θ.1 ≠ 0) (hr : r ≠ 0) :
    ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
      certificate.bracket 0 - centerBracketCoefficient θ * r = r ^ 2 * K θ r := by
  exact FrameKernelDataOn.bracketKernelCertificate data ⟨hθ, hr⟩

/-- Helper for Infrastructure I.16a: a domain-indexed frame package with a global punctured
    cover assembles the denominator-cleared center-residual certificate without
    committing the source to the canonical frame specification. -/
def FrameKernelDataOn.toKernelCertificate
    {β B : ℝ}
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    (radius : ℝ)
    (hradius : 0 < radius)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ r, θ.1 ≠ 0 → r ≠ 0 → D θ r)
    (hK : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-radius) radius)) :
    CenterResidualKernelCertificate β B :=
  CenterResidualKernelCertificate.of_rawBracketKernel K radius hradius hscale
    (fun θ r hθ hr ↦ data.bracketKernelCertificate (hcover θ r hθ hr)) hK

/-- Helper for Infrastructure I.16a: the global frame-kernel cover yields the
    complete mixed-variable uniform bound through the existing certificate API. -/
theorem FrameKernelDataOn.uniformBound_of_globalCover
    {β B : ℝ}
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    (radius : ℝ)
    (hradius : 0 < radius)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ r, θ.1 ≠ 0 → r ≠ 0 → D θ r)
    (hK : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-radius) radius)) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
      ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ (2 : ℕ)‖ ≤
      C * |θ.1| * |r| ^ (3 : ℝ) := by
  exact (data.toKernelCertificate radius hradius hscale hcover hK).uniformBound

/-- Infrastructure I.16a: a domain-indexed frame package gives the punctured physical
    center residual identity at every point of its source domain. -/
theorem FrameKernelDataOn.centerResidual_eq_cubicKernel
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hD : D θ r) :
    physicalCenterResidual θ r = (θ.1 * r ^ 3) • K θ r := by
  obtain ⟨certificate, hkernel⟩ := data.bracketKernelCertificate hD
  exact certificate.centerResidual_eq_cubicKernel hkernel

/-- Infrastructure I.16a: punctured canonical frame data transport the physical
    center residual directly to the denominator-cleared cubic kernel. -/
theorem CanonicalFrameKernelData.centerResidual_eq_cubicKernel
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (data : CanonicalFrameKernelData K)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hθ : θ.1 ≠ 0) (hr : r ≠ 0) :
    physicalCenterResidual θ r = (θ.1 * r ^ 3) • K θ r := by
  exact FrameKernelDataOn.centerResidual_eq_cubicKernel data ⟨hθ, hr⟩

/-- Helper for Infrastructure I.16a: the named physical residual vanishes on the
    zero-radius branch, with the evaluator definition hidden behind one rewrite. -/
theorem physicalCenterResidual_zeroRadius (θ : ℝ × ℝ × ℝ) :
    physicalCenterResidual θ 0 = 0 := by
  simpa only [physicalCenterResidual] using centerResidual_zeroRadius θ

/-- Infrastructure I.16a: a domain-indexed frame package extends its punctured identity
    to any predicate-covered region once the source supplies the two removable branches. -/
theorem FrameKernelDataOn.centerResidual_eq_cubicKernel_of_cover
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D P : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    (hscale : ∀ θ r, P θ r → θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ r, P θ r →
      θ.1 = 0 ∨ r = 0 ∨ D θ r)
    {θ : ℝ × ℝ × ℝ} {r : ℝ} (hP : P θ r) :
    physicalCenterResidual θ r = physicalCenterCubicWeight θ r • K θ r := by
  have hcover' : ∀ θ r, P θ r →
      θ.1 = 0 ∨ r = 0 ∨
        ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
          certificate.bracket 0 = spec.bracket θ r := by
    intro θ r hP'
    rcases hcover θ r hP' with hθ | hr | hD
    · exact Or.inl hθ
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (data.bracketCertificate hD))
  have hkernel' : ∀ θ r, P θ r → θ.1 ≠ 0 → r ≠ 0 →
      spec.bracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r := by
    intro θ r hP' hθ hr
    rcases hcover θ r hP' with hθzero | hrzero | hD
    · exact (hθ hθzero).elim
    · exact (hr hrzero).elim
    · exact data.bracketKernel θ r hD
  exact centerResidual_eq_cubicKernel_of_bracketCertificateCover
    (K := K) (W := fun θ r ↦ spec.bracket θ r) (P := P)
    hscale hcover' hkernel' hP

/-- Infrastructure I.16a: the covered raw evaluator is the prescribed quadratic drift plus the
    denominator-cleared cubic kernel, with both removable branches included. -/
theorem FrameKernelDataOn.fullCenterDisplacement_coord_zero_eq_drift_add_cubicKernel_of_cover
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D P : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    (hscale : ∀ θ r, P θ r → θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ r, P θ r →
      θ.1 = 0 ∨ r = 0 ∨ D θ r)
    {θ : ℝ × ℝ × ℝ} {r : ℝ} (hP : P θ r) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 =
      centerDriftCoefficient θ * r ^ 2 +
        physicalCenterCubicWeight θ r • K θ r := by
  have hres := data.centerResidual_eq_cubicKernel_of_cover hscale hcover hP
  unfold physicalCenterResidual at hres
  linarith

/-- Infrastructure I.16a: a scale-zero certificate together with the canonical frame data
    extends the punctured cubic identity across both removable branches. -/
theorem CanonicalFrameKernelData.centerResidual_eq_cubicKernel_of_removableBranches
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (data : CanonicalFrameKernelData K)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    {θ : ℝ × ℝ × ℝ} {r : ℝ} :
    physicalCenterResidual θ r = physicalCenterCubicWeight θ r • K θ r := by
  apply FrameKernelDataOn.centerResidual_eq_cubicKernel_of_cover
    (P := fun _ _ ↦ True) data
  · intro θ r _ hθ
    exact hscale θ r hθ
  · intro θ r _
    by_cases hθ : θ.1 = 0
    · exact Or.inl hθ
    · by_cases hr : r = 0
      · exact Or.inr (Or.inl hr)
      · exact Or.inr (Or.inr ⟨hθ, hr⟩)
  · trivial

/-- Infrastructure I.16a: punctured canonical signed-frame data directly assemble a
    denominator-cleared center-residual certificate for a continuous kernel.  The
    removable `θ.1 = 0` and `r = 0` branches remain in `hscale` and the kernel
    certificate interface, so no nonzero-denominator claim is imposed at a branch
    where the raw chart is singular. -/
def CenterResidualKernelCertificate.of_canonicalFrameData
    {β B : ℝ}
    (K : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (radius : ℝ)
    (hradius : 0 < radius)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (data : CanonicalFrameKernelData K)
    (hK : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-radius) radius)) :
    CenterResidualKernelCertificate β B :=
  FrameKernelDataOn.toKernelCertificate data radius hradius hscale
    (fun _θ _r hθ hr ↦ ⟨hθ, hr⟩) hK

/-- Infrastructure I.16a: a canonical frame package together with a base-shape
    zero-scale certificate produces the denominator-cleared center certificate;
    the radius-zero branch is supplied by the kernel certificate itself. -/
def CanonicalFrameKernelData.toKernelCertificate
    {β B : ℝ} {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (data : CanonicalFrameKernelData K)
    (radius : ℝ)
    (hradius : 0 < radius)
    (hbase : ∀ r : ℝ,
      (observableMap 0 (r, 2, 1)).fullCenterDisplacement 0 = 0)
    (hK : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-radius) radius)) :
    CenterResidualKernelCertificate β B :=
  CenterResidualKernelCertificate.of_canonicalFrameData K radius hradius
    (fun θ r hθ ↦ centerResidual_zeroScale_of_baseShapeCertificate θ r hθ (hbase r))
    data hK

end DFP.TwoLeg.Mixed
