module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeFrameQuadraticGermTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawFrameAngleSlopeCertificate
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawCanonicalFrameSlopeTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualSourceCertificate
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualSourceFromKernel

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
This file is the source-facing assembly boundary for the physical-drift proof.
The concrete frame calculation, raw slope factorization, and center quotient
kernel remain independent obligations.  Once those three certificates are
available, the parent theorem can consume the standard observable germs and
the mixed-variable center remainder estimate without reopening any evaluator.
-/

/-- Infrastructure for Appendix Lemma A.6: the three source certificates needed
    to assemble the physical amplitude, frame-angle, and center-residual outputs. -/
structure PhysicalDriftSourceCertificate (β B : ℝ) where
  amplitude : PhysicalAmplitudeFramePathCertificate (parameterSet β B)
  angle : MixedIndependentRawFrameAngleSlopeFactorCertificate (parameterSet β B)
  quotient : (ℝ × ℝ × ℝ) → ℝ → ℝ
  center : CenterResidualSourceCertificate β B quotient

/-- Helper for Appendix Lemma A.6: a denominator-cleared kernel certificate supplies the
    center component of the source assembly with its removable branches filled by the kernel. -/
noncomputable def PhysicalDriftSourceCertificate.ofAmplitudeAngleKernel
    {β B : ℝ}
    (amplitude : PhysicalAmplitudeFramePathCertificate (parameterSet β B))
    (angle : MixedIndependentRawFrameAngleSlopeFactorCertificate (parameterSet β B))
    (kernel : CenterResidualKernelCertificate β B) :
    PhysicalDriftSourceCertificate β B :=
  { amplitude := amplitude
    angle := angle
    quotient := kernelFilledCubicQuotient kernel
    center := kernel.toSourceCertificate }

/-- Helper for Appendix Lemma A.6: evaluating `input` on a parameter-radius
    pair exposes the canonical three coordinates without unfolding its definition. -/
theorem input_at_parameter_radius (z : (ℝ × ℝ × ℝ) × ℝ) :
    input z.1 z.2 =
      (z.2, 2 + z.1.2.1 * z.1.1 * z.2, 1 + z.1.2.2 * z.1.1 * z.2) := by
  have htuple : (z.1.1, z.1.2.1, z.1.2.2) = z.1 := by
    exact Prod.eta z.1
  calc
    input z.1 z.2 = input (z.1.1, z.1.2.1, z.1.2.2) z.2 := by
      rw [htuple]
    _ = (z.2, 2 + z.1.2.1 * z.1.1 * z.2,
        1 + z.1.2.2 * z.1.1 * z.2) := by
      exact input_apply z.1.1 z.1.2.1 z.1.2.2 z.2

/-- Helper for Appendix Lemma A.6: the physical frame-angle projection agrees
    pointwise with its canonical raw relative-frame normal form. -/
theorem physicalFrameAngle_uncurry_eventuallyEq_rawNormalForm
    {β B : ℝ}
    : ∀ θ, θ ∈ parameterSet β B →
      Function.uncurry
          (fun η r ↦ (observableMap η.1 (input η r)).frameAngleIncrement) =ᶠ[𝓝 (θ, 0)]
        Function.uncurry
          (fun η r ↦ mixedIndependentRawFrameAngle η.1 r
            (2 + η.2.1 * η.1 * r) (1 + η.2.2 * η.1 * r)) := by
  intro θ hθ
  filter_upwards [] with z
  change (observableMap z.1.1 (input z.1 z.2)).frameAngleIncrement =
    mixedIndependentRawFrameAngle z.1.1 z.2
      (2 + z.1.2.1 * z.1.1 * z.2) (1 + z.1.2.2 * z.1.1 * z.2)
  rw [input_at_parameter_radius z]
  exact mixedObservable_frameAngle_eq_independentRaw z.1.1 z.2
    (2 + z.1.2.1 * z.1.1 * z.2) (1 + z.1.2.2 * z.1.1 * z.2)

/-- Infrastructure I.16a: a raw-frame zero-radius/domain-cover certificate yields
    the physical frame-angle germ without first packaging a slope factorization. -/
theorem physicalFrameAngleGerm_of_rawFrameDomainCover
    {β B : ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : RawFrameSlopeDataOn D)
    (hcover : ∀ θ, θ ∈ parameterSet β B →
      ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
        z.2 = 0 ∨ D z.1 z.2) :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ (observableMap θ.1 (input θ r)).frameAngleIncrement)
      (parameterSet β B) 2
      (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) := by
  have hraw := rawFrameAngle_truncatedGerm_of_domainCover
    (K := parameterSet β B) data hcover
  have hmap := physicalFrameAngle_uncurry_eventuallyEq_rawNormalForm
    (β := β) (B := B)
  exact frameAngleGerm_of_uncurry_eventuallyEq hmap hraw

/- The amplitude path and the raw-frame domain cover are independent source
   certificates.  This theorem is the narrow assembly point for consumers that
   have not yet packaged the latter as a slope-factor certificate. -/

/-- Helper for Appendix Lemma A.6: an amplitude path certificate and a raw-frame
    zero-radius/domain cover jointly provide the two physical observable germs. -/
theorem physicalObservableGerms_of_amplitudeCertificate_and_rawFrameDomainCover
    {β B : ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (amplitude : PhysicalAmplitudeFramePathCertificate (parameterSet β B))
    (data : RawFrameSlopeDataOn D)
    (hcover : ∀ θ, θ ∈ parameterSet β B →
      ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
        z.2 = 0 ∨ D z.1 z.2) :
    IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio)
        (parameterSet β B) 3
        (fun n θ ↦
          (![1, 0,
            (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).frameAngleIncrement)
        (parameterSet β B) 2
        (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) := by
  have hamp := physicalAmplitudeTruncatedGerm_of_framePathCertificate amplitude
  have hangle := physicalFrameAngleGerm_of_rawFrameDomainCover
    (β := β) (B := B) data hcover
  exact ⟨hamp, hangle⟩

/-- Helper for Appendix Lemma A.6: the raw-frame domain-cover route and a center
    residual certificate jointly expose all three parent-facing outputs. -/
theorem physicalDriftOutputs_of_amplitudeCertificate_rawFrameDomainCover_and_center
    {β B : ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    {Q : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (amplitude : PhysicalAmplitudeFramePathCertificate (parameterSet β B))
    (data : RawFrameSlopeDataOn D)
    (hcover : ∀ θ, θ ∈ parameterSet β B →
      ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
        z.2 = 0 ∨ D z.1 z.2)
    (center : CenterResidualSourceCertificate β B Q) :
    (IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio)
        (parameterSet β B) 3
        (fun n θ ↦
          (![1, 0,
            (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).frameAngleIncrement)
        (parameterSet β B) 2
        (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n)) ∧
      (∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
        ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ (2 : ℕ)‖ ≤
        C * |θ.1| * |r| ^ (3 : ℝ)) := by
  have hgerms := physicalObservableGerms_of_amplitudeCertificate_and_rawFrameDomainCover
    (β := β) (B := B) amplitude data hcover
  have hcenter := center.uniformBound
  exact ⟨hgerms, hcenter⟩

/-- Helper for Appendix Lemma A.6: projection-domain and second-gradient
    positivity data canonically produce the raw-frame certificate required by
    the three-output assembly. -/
theorem physicalDriftOutputs_of_amplitudeCertificate_projectionDomain_and_gradient_cover_and_center
    {β B : ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    {Q : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (amplitude : PhysicalAmplitudeFramePathCertificate (parameterSet β B))
    (hD : ∀ θ r, D θ r → mixedRawProjectionDomain θ r)
    (hGlo : ∀ θ r, D θ r →
      0 < (independentRadiusSecondGradient (θ, r)).1)
    (hcover : ∀ θ, θ ∈ parameterSet β B →
      ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
        z.2 = 0 ∨ D z.1 z.2)
    (center : CenterResidualSourceCertificate β B Q) :
    (IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio)
        (parameterSet β B) 3
        (fun n θ ↦
          (![1, 0,
            (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).frameAngleIncrement)
        (parameterSet β B) 2
        (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n)) ∧
      (∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
        ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ (2 : ℕ)‖ ≤
        C * |θ.1| * |r| ^ (3 : ℝ)) := by
  have data : RawFrameSlopeDataOn D :=
    rawFrameSlopeDataOn_of_projectionDomain hD hGlo
  exact physicalDriftOutputs_of_amplitudeCertificate_rawFrameDomainCover_and_center
    (β := β) (B := B) (Q := Q) amplitude data hcover center

/- The positivity hypothesis above is automatic on a sufficiently small
   neighborhood of the removable radius.  Expose that reduction so source
   callers only need the projection-domain cover already produced by the raw
   chart. -/

/-- Helper for Appendix Lemma A.6: the analytic second-gradient factor and its
    unit zero-radius value upgrade a projection-domain cover to the complete
    raw-frame slope certificate. -/
theorem physicalDriftOutputs_of_amplitudeCertificate_projectionDomain_cover_and_center
    {β B : ℝ}
    {Q : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (amplitude : PhysicalAmplitudeFramePathCertificate (parameterSet β B))
    (hcoverDomain : ∀ θ, θ ∈ parameterSet β B →
      ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
        z.2 = 0 ∨ mixedRawProjectionDomain z.1 z.2)
    (center : CenterResidualSourceCertificate β B Q) :
    (IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio)
        (parameterSet β B) 3
        (fun n θ ↦
          (![1, 0,
            (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).frameAngleIncrement)
        (parameterSet β B) 2
        (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n)) ∧
      (∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
        ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ (2 : ℕ)‖ ≤
        C * |θ.1| * |r| ^ (3 : ℝ)) := by
  let D : (ℝ × ℝ × ℝ) → ℝ → Prop := fun θ r ↦
    mixedRawProjectionDomain θ r ∧
      0 < (independentRadiusSecondGradient (θ, r)).1
  have hD : ∀ θ r, D θ r → mixedRawProjectionDomain θ r := by
    intro θ r h
    exact h.1
  have hGlo : ∀ θ r, D θ r →
      0 < (independentRadiusSecondGradient (θ, r)).1 := by
    intro θ r h
    exact h.2
  have hcover : ∀ θ, θ ∈ parameterSet β B →
      ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
        z.2 = 0 ∨ D z.1 z.2 := by
    intro θ hθ
    have hdomain := hcoverDomain θ hθ
    have hgradientContinuous : ContinuousAt
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusSecondGradient z).1) (θ, 0) :=
      continuousAt_fst.comp (independentRadiusSecondGradient_analyticAt θ).continuousAt
    have hgradient : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
        0 < (independentRadiusSecondGradient z).1 := by
      apply hgradientContinuous.eventually
      have hbase :
          (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
            (independentRadiusSecondGradient z).1) (θ, 0) = 1 := by
        exact congrArg Prod.fst (independentRadiusSecondGradient_zero θ)
      rw [hbase]
      have hone : (0 : ℝ) < 1 := by norm_num
      exact Ioi_mem_nhds hone
    filter_upwards [hdomain, hgradient] with z hz hpositive
    by_cases hz0 : z.2 = 0
    · exact Or.inl hz0
    · rcases hz with hz | hz
      · exact False.elim (hz0 hz)
      · exact Or.inr ⟨hz, hpositive⟩
  exact physicalDriftOutputs_of_amplitudeCertificate_projectionDomain_and_gradient_cover_and_center
    (β := β) (B := B) (Q := Q) (D := D) amplitude hD hGlo hcover center

/-- Helper for Appendix Lemma A.6: compactness combines the raw projection tube
    with the positive second-gradient neighborhood into one uniform source tube. -/
theorem mixedRawProjectionDomain_and_secondGradient_uniformTube
    (β B : ℝ) (hβ_small : β < 1 / 4) (hB : 0 ≤ B) :
    ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
      r = 0 ∨
        (mixedRawProjectionDomain θ r ∧
          0 < (independentRadiusSecondGradient (θ, r)).1) := by
  obtain ⟨δDomain, hδDomain, hDomain⟩ :=
    mixedRawProjectionDomain_uniformTube β B hβ_small hB
  have hpointwise : ∀ θ, θ ∈ parameterSet β B →
      ∀ᶠ z : ℝ × (ℝ × ℝ × ℝ) in 𝓝 (0, θ),
        z.1 = 0 ∨ 0 < (independentRadiusSecondGradient (z.2, z.1)).1 := by
    intro θ hθ
    rw [nhds_swap]
    change ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      z.2 = 0 ∨ 0 < (independentRadiusSecondGradient z).1
    have hcontinuous : ContinuousAt
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusSecondGradient z).1) (θ, 0) :=
      continuousAt_fst.comp (independentRadiusSecondGradient_analyticAt θ).continuousAt
    have hpositive : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
        0 < (independentRadiusSecondGradient z).1 := by
      apply hcontinuous.eventually
      have hbase :
          (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
            (independentRadiusSecondGradient z).1) (θ, 0) = 1 := by
        exact congrArg Prod.fst (independentRadiusSecondGradient_zero θ)
      rw [hbase]
      have hone : (0 : ℝ) < 1 := by norm_num
      exact Ioi_mem_nhds hone
    filter_upwards [hpositive] with z hz
    by_cases hz0 : z.2 = 0
    · exact Or.inl hz0
    · exact Or.inr hz
  obtain ⟨δGradient, hδGradient, hGradient⟩ :=
    FiniteTaylorJet.compactFiberNormRadius
      (X := ℝ) (Y := ℝ × ℝ × ℝ)
      (P := fun r θ ↦ r = 0 ∨
        0 < (independentRadiusSecondGradient (θ, r)).1)
      (parameterSet_isCompact β B) hpointwise
  have hδ : 0 < min δDomain δGradient := lt_min hδDomain hδGradient
  refine ⟨min δDomain δGradient, hδ, ?_⟩
  intro θ hθ r hr
  have hrDomain : |r| < δDomain :=
    lt_of_lt_of_le hr (min_le_left δDomain δGradient)
  have hrGradient : |r| < δGradient :=
    lt_of_lt_of_le hr (min_le_right δDomain δGradient)
  have hDomainAt := hDomain θ hθ r hrDomain
  have hGradientAt := hGradient θ hθ r hrGradient
  rcases hDomainAt with hz | hdomain
  · exact Or.inl hz
  · rcases hGradientAt with hz | hpositive
    · exact Or.inl hz
    · exact Or.inr ⟨hdomain, hpositive⟩

/-- Helper for Appendix Lemma A.6: the uniform projection/positivity tube
    produces the complete signed raw-frame slope data at every punctured point. -/
theorem rawFrameSlopeData_uniformTube
    (β B : ℝ) (hβ_small : β < 1 / 4) (hB : 0 ≤ B) :
    ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
      r = 0 ∨ RawFrameSlopeData θ r := by
  obtain ⟨δ, hδ, htube⟩ :=
    mixedRawProjectionDomain_and_secondGradient_uniformTube β B hβ_small hB
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ r hr
  rcases htube θ hθ r hr with hz | hdata
  · exact Or.inl hz
  · exact Or.inr (RawFrameSlopeData.of_projectionDomain_and_gradient θ r
      hdata.1 hdata.2)

/- The uniform tube also supplies the angle and center outputs without requiring
   callers to package a separate quotient certificate.  The amplitude path
   remains explicit because it is independent of the raw-frame chart. -/

/-- Helper for Appendix Lemma A.6: a uniform projection/gradient tube and an
    amplitude path certificate assemble both observable germs and the automatic
    mixed center-residual bound. -/
theorem physicalDriftOutputs_of_amplitudeCertificate_uniformProjectionTube
    {β B : ℝ}
    (amplitude : PhysicalAmplitudeFramePathCertificate (parameterSet β B))
    (hβ_small : β < 1 / 4) (hB : 0 ≤ B) :
    (IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio)
        (parameterSet β B) 3
        (fun n θ ↦
          (![1, 0,
            (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).frameAngleIncrement)
        (parameterSet β B) 2
        (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n)) ∧
      (∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
        ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ (2 : ℕ)‖ ≤
        C * |θ.1| * |r| ^ (3 : ℝ)) := by
  have hamp := physicalAmplitudeTruncatedGerm_of_framePathCertificate amplitude
  have hraw := rawFrameAngle_truncatedGerm_of_parameterSet β B hβ_small
  have hmap := physicalFrameAngle_uncurry_eventuallyEq_rawNormalForm
    (β := β) (B := B)
  have hangle := frameAngleGerm_of_uncurry_eventuallyEq hmap hraw
  have hcenter := mixedCenterResidual_uniformBound_of_uniformProjectionTube_zeroScale
    β B hβ_small hB
  exact ⟨⟨hamp, hangle⟩, hcenter⟩

/-- Appendix Lemma A.6: a source certificate assembles the physical amplitude
    and frame-angle truncated germs on the same parameter set. -/
theorem PhysicalDriftSourceCertificate.observableGerms
    {β B : ℝ}
    (certificate : PhysicalDriftSourceCertificate β B) :
    IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio)
        (parameterSet β B) 3
        (fun n θ ↦
          (![1, 0,
            (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).frameAngleIncrement)
        (parameterSet β B) 2
        (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) := by
  have hamp := physicalAmplitudeTruncatedGerm_of_framePathCertificate
    certificate.amplitude
  have hangleRaw :=
    mixedIndependentRawFrameAngleAlongInput_truncatedGerm_of_factorCertificate
      certificate.angle
  have hangleMap :=
    physicalFrameAngle_uncurry_eventuallyEq_rawNormalForm (β := β) (B := B)
  have hangle := frameAngleGerm_of_uncurry_eventuallyEq hangleMap hangleRaw
  exact ⟨hamp, hangle⟩

/-- Appendix Lemma A.6: a source center certificate exposes the uniform
    mixed-variable cubic remainder bound in the exact parent-facing form. -/
theorem PhysicalDriftSourceCertificate.centerResidualUniformBound
    {β B : ℝ}
    (certificate : PhysicalDriftSourceCertificate β B) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
      ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ (2 : ℕ)‖ ≤
      C * |θ.1| * |r| ^ (3 : ℝ) := by
  exact certificate.center.uniformBound

/-- Appendix Lemma A.6: all source-facing physical-drift obligations are
    available together as one consumable assembly theorem. -/
theorem PhysicalDriftSourceCertificate.assembledOutputs
    {β B : ℝ}
    (certificate : PhysicalDriftSourceCertificate β B) :
    (IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio)
        (parameterSet β B) 3
        (fun n θ ↦
          (![1, 0,
            (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).frameAngleIncrement)
        (parameterSet β B) 2
        (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n)) ∧
      (∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
        ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ (2 : ℕ)‖ ≤
        C * |θ.1| * |r| ^ (3 : ℝ)) := by
  have hgerms := certificate.observableGerms
  have hcenter := certificate.centerResidualUniformBound
  exact ⟨hgerms, hcenter⟩

/-- Helper for Appendix Lemma A.6: amplitude, angle, and denominator-cleared kernel
    certificates directly expose all three parent-facing physical-drift outputs. -/
theorem physicalDriftOutputs_of_amplitudeAngleKernel
    {β B : ℝ}
    (amplitude : PhysicalAmplitudeFramePathCertificate (parameterSet β B))
    (angle : MixedIndependentRawFrameAngleSlopeFactorCertificate (parameterSet β B))
    (kernel : CenterResidualKernelCertificate β B) :
    (IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio)
        (parameterSet β B) 3
        (fun n θ ↦
          (![1, 0,
            (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).frameAngleIncrement)
        (parameterSet β B) 2
        (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n)) ∧
      (∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
        ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ (2 : ℕ)‖ ≤
        C * |θ.1| * |r| ^ (3 : ℝ)) := by
  exact (PhysicalDriftSourceCertificate.ofAmplitudeAngleKernel
    amplitude angle kernel).assembledOutputs

end DFP.TwoLeg.Mixed
