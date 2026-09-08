module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseScaleJetCertificate
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseScaleJetCertificate

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

/-!
# A source-facing second scale-jet certificate

This companion isolates the only source calculation still needed by the cubic transverse
estimate: the second derivative in the signed scale variable.  The source side may provide
that calculation either as a derivative of the scalar transverse evaluation or directly as a
derivative of the bundled `fderiv` family.  The adapters below convert either form into the
canonical `iteratedFDeriv ℝ 2` statement.
-/

/-- Helper for Lemma 4.15: zero second scale derivatives after evaluating a
continuous-linear-map-valued family imply a zero bundled second scale jet. -/
theorem iteratedFDeriv_two_eq_zero_of_fderiv_apply_second
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (family : ℝ → Y →L[ℝ] ℝ)
    (hregular : ContDiffAt ℝ 2 family 0)
    (hsecond : ∀ w : Y,
      HasDerivAt
        (fun ε : ℝ ↦ (fderiv ℝ family ε) 1 w) 0 0) :
    iteratedFDeriv ℝ 2 family 0 = 0 := by
  apply ContinuousMultilinearMap.ext
  intro directions
  apply ContinuousLinearMap.ext
  intro w
  rw [iteratedFDeriv_two_apply]
  have honeNeZero : (1 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hfamilyFDeriv : DifferentiableAt ℝ (fderiv ℝ family) 0 := by
    have horder : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞) := by
      norm_num
    exact hregular.fderiv_right horder |>.differentiableAt honeNeZero
  have hfamilyHasDeriv : HasDerivAt (fderiv ℝ family)
      (deriv (fderiv ℝ family) 0) 0 :=
    hfamilyFDeriv.hasDerivAt
  have honeConstant : HasDerivAt (fun _ : ℝ ↦ (1 : ℝ)) 0 0 :=
    hasDerivAt_const 0 1
  have hfirstApplyRaw := hfamilyHasDeriv.clm_apply honeConstant
  have hfirstApply : HasDerivAt
      (fun ε : ℝ ↦ (fderiv ℝ family ε) 1)
      ((deriv (fderiv ℝ family) 0) 1) 0 := by
    apply hfirstApplyRaw.congr_deriv
    simp only [ContinuousLinearMap.map_zero, add_zero]
  have hwConstant : HasDerivAt (fun _ : ℝ ↦ w) 0 0 :=
    hasDerivAt_const 0 w
  have hsecondApplyRaw := hfirstApply.clm_apply hwConstant
  have hsecondApply : HasDerivAt
      (fun ε : ℝ ↦ (fderiv ℝ family ε) 1 w)
      ((deriv (fderiv ℝ family) 0) 1 w) 0 := by
    apply hsecondApplyRaw.congr_deriv
    simp only [ContinuousLinearMap.map_zero, add_zero]
  have hunitValue : (deriv (fderiv ℝ family) 0) 1 w = 0 :=
    hsecondApply.unique (hsecond w)
  have hunitValue' :
      (fderiv ℝ (fderiv ℝ family) 0) 1 1 w = 0 := by
    rw [fderiv_apply_one_eq_deriv]
    exact hunitValue
  have hdirection0 : directions 0 = directions 0 • (1 : ℝ) := by
    simp
  have hdirection1 : directions 1 = directions 1 • (1 : ℝ) := by
    simp
  rw [hdirection0, hdirection1]
  rw [map_smul]
  rw [map_smul]
  simp only [smul_apply, smul_eq_mul]
  rw [hunitValue']
  simp

/-- Helper for Lemma 4.15: vanishing second derivatives of every scalar evaluation
force the bundled second scale jet to vanish. -/
theorem iteratedFDeriv_two_eq_zero_of_scalar_second
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (family : ℝ → Y →L[ℝ] ℝ)
    (hregular : ContDiffAt ℝ 2 family 0)
    (hsecond : ∀ w : Y,
      HasDerivAt
        (fun ε : ℝ ↦ deriv (fun t : ℝ ↦ (family t) w) ε) 0 0) :
    iteratedFDeriv ℝ 2 family 0 = 0 := by
  have htwoFinite :
      (2 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    norm_num
  have htwoNeZero : (2 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hregularEvent : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      ContDiffAt ℝ 2 family ε :=
    hregular.eventually htwoFinite
  have hfamilyDiff : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      DifferentiableAt ℝ family ε := by
    filter_upwards [hregularEvent] with ε hε
    exact hε.differentiableAt htwoNeZero
  apply iteratedFDeriv_two_eq_zero_of_fderiv_apply_second family hregular
  intro w
  have heq : (fun ε : ℝ ↦ (fderiv ℝ family ε) 1 w) =ᶠ[𝓝 (0 : ℝ)]
      (fun ε : ℝ ↦ deriv (fun t : ℝ ↦ (family t) w) ε) := by
    filter_upwards [hfamilyDiff] with ε hε
    have hconstant : DifferentiableAt ℝ (fun _ : ℝ ↦ w) ε :=
      differentiableAt_const _
    have happly := fderiv_clm_apply hε hconstant
    have happlyOne := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) happly
    rw [fderiv_apply_one_eq_deriv] at happlyOne
    have hconstFDeriv : fderiv ℝ (fun _ : ℝ ↦ w) ε = 0 :=
      (hasFDerivAt_const w ε).fderiv
    rw [hconstFDeriv] at happlyOne
    have hzeroComp : ((family ε).comp (0 : ℝ →L[ℝ] Y)) 1 = 0 := by
      simp
    have hflip : ((fderiv ℝ family ε).flip w) 1 =
        (fderiv ℝ family ε) 1 w := by
      rfl
    rw [add_apply, hzeroComp, hflip] at happlyOne
    simpa only [zero_add] using happlyOne.symm
  exact (hsecond w).congr_of_eventuallyEq heq

/-! The concrete certificate contains only the source identity.  Joint analyticity already
supplies the regularity required by the generic adapter. -/

/-- Helper for Lemma 4.15: source-side scalar second-scale stationarity for every
nearby transverse parameter and every transverse direction. -/
structure LowGradientTransverseSecondScaleCertificate : Prop where
  scalar_second :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ), ∀ w : ℝ × ℝ,
      HasDerivAt
        (fun ε : ℝ ↦ deriv
          (fun t : ℝ ↦ (lowGradientTransverseFDerivFamily z t) w) ε) 0 0

/-- Helper for Lemma 4.15: the source-side scalar certificate exposes exactly the
eventual second iterated scale jet consumed by the cubic estimate. -/
theorem LowGradientTransverseSecondScaleCertificate.eventually_secondScaleJet
    (certificate : LowGradientTransverseSecondScaleCertificate) :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2 (lowGradientTransverseFDerivFamily z) 0 = 0 := by
  filter_upwards [lowGradientTransverseFDerivFamily_eventually_contDiffAt_two,
    certificate.scalar_second] with z hregular hsecond
  exact iteratedFDeriv_two_eq_zero_of_scalar_second
    (lowGradientTransverseFDerivFamily z) hregular hsecond

end DFP.SecondLeg
