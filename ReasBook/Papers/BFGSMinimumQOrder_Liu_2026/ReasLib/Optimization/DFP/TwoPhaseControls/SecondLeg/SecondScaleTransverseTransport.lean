module

public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import ReasLib.Analysis.Calculus.ContDiff.ThirdMixedJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicJet
import all ReasLib.Analysis.Calculus.ContDiff.ThirdMixedJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicJet

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.Calculus

/-- Helper for Infrastructure I.16a: a vanishing third derivative in two scale
directions and one parameter direction makes the derivative of the corresponding
partial-derivative slice stationary to second scale order. -/
theorem hasDerivAt_deriv_partialFDeriv_of_thirdJet_eq_zero
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (f : ℝ × Z → ℝ) (z w : Z)
    (hf : AnalyticAt ℝ f ((0 : ℝ), z))
    (hthird : iteratedFDeriv ℝ 3 f ((0 : ℝ), z)
      ![((1 : ℝ), (0 : Z)), ((1 : ℝ), (0 : Z)), ((0 : ℝ), w)] = 0) :
    HasDerivAt
      (fun ε : ℝ ↦ deriv
        (fun t : ℝ ↦
          (fderiv ℝ (fun y : Z ↦ f (t, y)) z) w) ε)
      0 0 := by
  let a : ℝ × Z := ((0 : ℝ), z)
  let scale : ℝ × Z := ((1 : ℝ), (0 : Z))
  let transverse : ℝ × Z := ((0 : ℝ), w)
  let line : ℝ → ℝ × Z := fun ε ↦ (ε, z)
  let derivative : (ℝ × Z) → (ℝ × Z) →L[ℝ] ℝ := fderiv ℝ f
  let secondDerivative : (ℝ × Z) →
      (ℝ × Z) →L[ℝ] (ℝ × Z) →L[ℝ] ℝ :=
    fderiv ℝ derivative
  let fullSlice : ℝ → ℝ := fun ε ↦ derivative (line ε) transverse
  let fullSliceDerivative : ℝ → ℝ :=
    fun ε ↦ secondDerivative (line ε) scale transverse
  let partialSlice : ℝ → ℝ :=
    fun ε ↦ (fderiv ℝ (fun y : Z ↦ f (ε, y)) z) w
  have hlineAt (ε : ℝ) : HasDerivAt line scale ε := by
    have hfirst : HasDerivAt (fun t : ℝ ↦ t) 1 ε :=
      hasDerivAt_id ε
    have hsecond : HasDerivAt (fun _ : ℝ ↦ z) 0 ε :=
      hasDerivAt_const ε z
    have hproduct := hfirst.prodMk hsecond
    simpa only [line, scale] using hproduct
  have hlineZero : line 0 = a := by
    rfl
  have hlineTendsto : Tendsto line (𝓝 (0 : ℝ)) (𝓝 a) := by
    rw [← hlineZero]
    exact (hlineAt 0).continuousAt
  have hfEventually : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      AnalyticAt ℝ f (line ε) :=
    hlineTendsto.eventually hf.eventually_analyticAt
  have hderivativeEventually : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      DifferentiableAt ℝ derivative (line ε) := by
    filter_upwards [hfEventually] with ε hε
    have horder : (1 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞) := by
      norm_num
    have hcontDiff : ContDiffAt ℝ 1 derivative (line ε) :=
      hε.contDiffAt.fderiv_right horder
    exact hcontDiff.differentiableAt one_ne_zero
  have hfullSliceDerivative :
      deriv fullSlice =ᶠ[𝓝 (0 : ℝ)] fullSliceDerivative := by
    filter_upwards [hderivativeEventually] with ε hε
    have halong := hε.hasFDerivAt.comp_hasDerivAt ε (hlineAt ε)
    have hconstant : HasDerivAt (fun _ : ℝ ↦ transverse) 0 ε :=
      hasDerivAt_const ε transverse
    have hevaluated := halong.clm_apply hconstant
    have hevaluated' : HasDerivAt fullSlice
        (secondDerivative (line ε) scale transverse) ε := by
      apply hevaluated.congr_deriv
      simp only [ContinuousLinearMap.map_zero, add_zero, secondDerivative]
    exact hevaluated'.deriv
  have hsecondDerivativeDifferentiable :
      DifferentiableAt ℝ secondDerivative a := by
    have horderFirst : (2 : WithTop ℕ∞) + 1 ≤ (4 : WithTop ℕ∞) := by
      norm_num
    have hderivativeContDiff : ContDiffAt ℝ 2 derivative a :=
      hf.contDiffAt.fderiv_right horderFirst
    have horderSecond : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞) := by
      norm_num
    have hsecondContDiff : ContDiffAt ℝ 1 secondDerivative a :=
      hderivativeContDiff.fderiv_right horderSecond
    exact hsecondContDiff.differentiableAt one_ne_zero
  have hsecondAlongLine : HasDerivAt
      (secondDerivative ∘ line)
      (fderiv ℝ secondDerivative a scale) 0 := by
    have hchain := hsecondDerivativeDifferentiable.hasFDerivAt.comp_hasDerivAt
      0 (hlineAt 0)
    simpa only [hlineZero] using hchain
  have hscaleConstant : HasDerivAt (fun _ : ℝ ↦ scale) 0 0 :=
    hasDerivAt_const 0 scale
  have htransverseConstant : HasDerivAt (fun _ : ℝ ↦ transverse) 0 0 :=
    hasDerivAt_const 0 transverse
  have hfirstEvaluation := hsecondAlongLine.clm_apply hscaleConstant
  have hsecondEvaluation := hfirstEvaluation.clm_apply htransverseConstant
  have hthirdValue :
      (fderiv ℝ secondDerivative a) scale scale transverse = 0 := by
    have hthirdFormula :
        iteratedFDeriv ℝ 3 f a ![scale, scale, transverse] =
          (fderiv ℝ secondDerivative a) scale scale transverse := by
      rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
      rfl
    rw [← hthirdFormula]
    simpa only [a, scale, transverse] using hthird
  have hfullSliceDerivativeAt :
      HasDerivAt fullSliceDerivative 0 0 := by
    apply hsecondEvaluation.congr_deriv
    simp only [ContinuousLinearMap.map_zero, add_zero, hthirdValue]
  have hderivFullSlice : HasDerivAt (deriv fullSlice) 0 0 :=
    hfullSliceDerivativeAt.congr_of_eventuallyEq hfullSliceDerivative
  have hpartialFull :
      partialSlice =ᶠ[𝓝 (0 : ℝ)] fullSlice := by
    filter_upwards [hfEventually] with ε hε
    have hembedding : HasFDerivAt (fun y : Z ↦ (ε, y))
        (ContinuousLinearMap.inr ℝ ℝ Z) z :=
      hasFDerivAt_prodMk_right ε z
    have hchain := hε.differentiableAt.hasFDerivAt.comp z hembedding
    have hchainApplied := congrArg (fun L : Z →L[ℝ] ℝ ↦ L w) hchain.fderiv
    simpa only [partialSlice, fullSlice, derivative, line, transverse,
      Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using hchainApplied
  exact hderivFullSlice.congr_of_eventuallyEq hpartialFull.deriv

/-- Infrastructure I.16a: local vanishing of the pure second scale jet transports
to scalar second-scale stationarity of every transverse derivative evaluation. -/
theorem hasDerivAt_deriv_partialFDeriv_of_eventually_scaleSecondJet_zero
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (f : ℝ × Z → ℝ) (z : Z)
    (hf : AnalyticAt ℝ f ((0 : ℝ), z))
    (hscale : ∀ᶠ y : Z in 𝓝 z,
      iteratedFDeriv ℝ 2 (fun ε : ℝ ↦ f (ε, y)) 0 = 0) :
    ∀ w : Z,
      HasDerivAt
        (fun ε : ℝ ↦ deriv
          (fun t : ℝ ↦
            (fderiv ℝ (fun y : Z ↦ f (t, y)) z) w) ε)
        0 0 := by
  let scale : ℝ × Z := ((1 : ℝ), (0 : Z))
  let inclusion : Z →L[ℝ] ℝ × Z := ContinuousLinearMap.inr ℝ ℝ Z
  have hparameterAnalytic : ∀ᶠ y : Z in 𝓝 z,
      AnalyticAt ℝ f ((0 : ℝ), y) := by
    have hinclusionContinuous : ContinuousAt
        (fun y : Z ↦ ((0 : ℝ), y)) z := by
      fun_prop
    exact hinclusionContinuous.eventually hf.eventually_analyticAt
  have hfullScale : (fun y : Z ↦
      iteratedFDeriv ℝ 2 f ((0 : ℝ), y) ![scale, scale]) =ᶠ[𝓝 z]
        (fun _ : Z ↦ (0 : ℝ)) := by
    filter_upwards [hscale, hparameterAnalytic] with y hy hfy
    have hsliceValue := congrArg
      (fun jet : ℝ [×2]→L[ℝ] ℝ ↦ jet ![(1 : ℝ), (1 : ℝ)]) hy
    have hsliceFull :=
      iteratedFDeriv_two_affineScaleSlice_eq_full f y hfy.contDiffAt
    rw [hsliceFull] at hsliceValue
    simpa only [scale, zero_apply] using hsliceValue
  intro w
  have hthirdParameter :
      iteratedFDeriv ℝ 3 f ((0 : ℝ), z)
        ![inclusion w, scale, scale] = 0 := by
    have hzero :
        (fun y : Z ↦
          iteratedFDeriv ℝ 2 f (inclusion y) ![scale, scale]) =ᶠ[𝓝 z]
          (fun _ : Z ↦ (0 : ℝ)) := by
      simpa only [inclusion, ContinuousLinearMap.inr_apply] using hfullScale
    have hregular : ContDiffAt ℝ 3 f (inclusion z) := by
      simpa only [inclusion, ContinuousLinearMap.inr_apply] using hf.contDiffAt
    have hthird :=
      iteratedFDeriv_three_eq_zero_of_eventually_secondJet_zero
        (f := f) (c := inclusion) scale scale hregular hzero w
    simpa only [inclusion, ContinuousLinearMap.inr_apply] using hthird
  have hthirdScaleFirst :
      iteratedFDeriv ℝ 3 f ((0 : ℝ), z)
        ![scale, scale, inclusion w] = 0 := by
    let directions : Fin 3 → ℝ × Z := ![scale, scale, inclusion w]
    let permutation : Equiv.Perm (Fin 3) := Equiv.swap 0 2
    have hperm := hf.contDiffAt.iteratedFDeriv_comp_perm directions permutation
    have hpermuted :
        directions ∘ permutation = ![inclusion w, scale, scale] := by
      funext i
      fin_cases i
      · rfl
      · rfl
      · rfl
    rw [hpermuted] at hperm
    rw [← hperm]
    exact hthirdParameter
  simpa only [scale, inclusion, ContinuousLinearMap.inr_apply] using
    hasDerivAt_deriv_partialFDeriv_of_thirdJet_eq_zero
      f z w hf hthirdScaleFirst

end DFP.Calculus

namespace DFP.SecondLeg

/-- Infrastructure I.16a: a source proof of the pure second scale-jet
cancellation for the low second-leg factor supplies the scalar second-scale
stationarity required by the transverse cubic estimate. -/
theorem lowGradientTransverseFDerivFamily_scalar_secondScale_eventually_of_pureSecondScaleJet
    (hscale : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2
        (fun ε : ℝ ↦ lowGradientFactor (ε, z)) 0 = 0) :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ), ∀ w : ℝ × ℝ,
      HasDerivAt
        (fun ε : ℝ ↦ deriv
          (fun t : ℝ ↦
            (lowGradientTransverseFDerivFamily z t) w) ε)
        0 0 := by
  have hanalytic : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      AnalyticAt ℝ lowGradientFactor ((0 : ℝ), z) := by
    have hslice : ContinuousAt
        (fun z : ℝ × ℝ ↦ ((0 : ℝ), z))
        ((2, 1) : ℝ × ℝ) := by
      fun_prop
    exact hslice.eventually lowGradientFactor_analyticAt.eventually_analyticAt
  have hscaleLocal : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      ∀ᶠ y : ℝ × ℝ in 𝓝 z,
        iteratedFDeriv ℝ 2
          (fun ε : ℝ ↦ lowGradientFactor (ε, y)) 0 = 0 :=
    eventually_eventually_nhds.2 hscale
  filter_upwards [hscaleLocal, hanalytic] with z hz hregular
  simpa only [lowGradientTransverseFDerivFamily, lowGradientFactor] using
    DFP.Calculus.hasDerivAt_deriv_partialFDeriv_of_eventually_scaleSecondJet_zero
      lowGradientFactor z hregular hz

end DFP.SecondLeg
