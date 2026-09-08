module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ScaleStationarityBridge
public import ReasLib.Analysis.Calculus.ContDiff.CrossDerivative
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicJet

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

/-!
This module exposes the scale/transverse cancellation away from the single reference
point.  The positivity assumptions are exactly the domain on which the zero-scale
stationarity formula is available.
-/

/-- Helper for Infrastructure I.16a and Lemma 4.15: an analytic scalar family whose
scale derivative vanishes on the positive transverse slice has zero scale/transverse
Hessian at every positive transverse base point. -/
theorem iteratedFDeriv_scale_transverse_eq_zero_at_positive
    (f : (ℝ × ℝ × ℝ) → ℝ) (p h : ℝ)
    (hp : 0 < p) (hh : 0 < h)
    (hf : AnalyticAt ℝ f (0, p, h))
    (hscale : ∀ p h : ℝ, 0 < p → 0 < h →
      HasDerivAt (fun ε : ℝ ↦ f (ε, p, h)) 0 0)
    (v : ℝ × ℝ × ℝ) (hv : v.1 = 0) :
    iteratedFDeriv ℝ 2 f (0, p, h)
      ![((1, 0, 0) : ℝ × ℝ × ℝ), v] = 0 := by
  let a : ℝ × ℝ × ℝ := (0, p, h)
  let u : ℝ × ℝ × ℝ := (1, 0, 0)
  let line : ℝ → ℝ × ℝ × ℝ := fun t ↦ a + t • v
  have hline_continuous : ContinuousAt line 0 := by
    dsimp only [line]
    fun_prop
  have hline_zero : line 0 = a := by
    simp only [line, zero_smul, add_zero]
  have hline : Tendsto line (𝓝 0) (𝓝 a) := by
    rw [← hline_zero]
    exact hline_continuous
  have hanalytic : ∀ᶠ t in 𝓝 (0 : ℝ), AnalyticAt ℝ f (line t) :=
    hline.eventually hf.eventually_analyticAt
  have hp_nhds : ∀ᶠ x in 𝓝 a, 0 < x.2.1 := by
    have hcoord : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.1) a := by
      fun_prop
    exact hcoord.eventually (Ioi_mem_nhds hp)
  have hh_nhds : ∀ᶠ x in 𝓝 a, 0 < x.2.2 := by
    have hcoord : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.2) a := by
      fun_prop
    exact hcoord.eventually (Ioi_mem_nhds hh)
  have hp_line : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (line t).2.1 :=
    hline.eventually hp_nhds
  have hh_line : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (line t).2.2 :=
    hline.eventually hh_nhds
  have hzero : ∀ᶠ t in 𝓝 (0 : ℝ),
      fderiv ℝ f (a + t • v) u = 0 := by
    filter_upwards [hanalytic, hp_line, hh_line] with t hft hpt hht
    let x : ℝ × ℝ × ℝ := line t
    have hx_scale : x.1 = 0 := by
      simp [x, line, a, hv, smul_eq_mul]
    have hx_eq : ((0, x.2.1, x.2.2) : ℝ × ℝ × ℝ) = x := by
      apply Prod.ext
      · simp only [x, hx_scale]
      · apply Prod.ext
        · rfl
        · rfl
    have hinner : HasDerivAt
        (fun ε : ℝ ↦ ((ε, x.2.1, x.2.2) : ℝ × ℝ × ℝ)) u 0 := by
      have hpconst : HasDerivAt (fun _ : ℝ ↦ x.2.1) 0 0 :=
        hasDerivAt_const 0 x.2.1
      have hhconst : HasDerivAt (fun _ : ℝ ↦ x.2.2) 0 0 :=
        hasDerivAt_const 0 x.2.2
      have hprod := (hasDerivAt_id (0 : ℝ)).prodMk (hpconst.prodMk hhconst)
      simpa only [u, id_eq] using hprod
    have hft' : DifferentiableAt ℝ f
        ((0, x.2.1, x.2.2) : ℝ × ℝ × ℝ) := by
      simpa only [hx_eq] using hft.differentiableAt
    have hchain := hft'.hasFDerivAt.comp_hasDerivAt 0 hinner
    have hstationary := hscale x.2.1 x.2.2 hpt hht
    have hvalue : fderiv ℝ f
        ((0, x.2.1, x.2.2) : ℝ × ℝ × ℝ) u = 0 :=
      hchain.unique hstationary
    simpa only [x, line, hx_eq] using hvalue
  have hf2 : ContDiffAt ℝ 2 f (0, p, h) := hf.contDiffAt
  have hzero_at_a : ∀ᶠ t in 𝓝 (0 : ℝ),
      fderiv ℝ f (a + t • v) u = 0 := by
    simpa only [a] using hzero
  have hresult :=
    hf2.iteratedFDeriv_two_apply_eq_zero_of_eventually_fderiv_line_eq_zero
      ((1, 0, 0) : ℝ × ℝ × ℝ) v hzero_at_a
  simpa only [a, u] using hresult

/-! The next adapter identifies a directional derivative of a partial derivative
with the corresponding mixed Hessian.  Keeping this interface separate avoids
unfolding the concrete gradient-factor construction in downstream estimates. -/

/-- Helper for Infrastructure I.16a and Lemma 4.15: a zero scale/transverse
Hessian forces every fixed transverse direction of the partial transverse
derivative to have zero scale derivative. -/
theorem partialFDeriv_apply_hasDerivAt_of_scaleTransverseHessian
    (f : ℝ × (ℝ × ℝ) → ℝ) (p h : ℝ) (w : ℝ × ℝ)
    (hf : AnalyticAt ℝ f (0, p, h))
    (hzero : iteratedFDeriv ℝ 2 f (0, p, h)
      ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, w.1, w.2)] = 0) :
    HasDerivAt (fun ε : ℝ ↦
      (fderiv ℝ (fun y : ℝ × ℝ ↦ f (ε, y)) (p, h)) w) 0 0 := by
  let c : ℝ × ℝ := (p, h)
  let a : ℝ × (ℝ × ℝ) := ((0 : ℝ), c)
  let path : ℝ → ℝ × (ℝ × ℝ) :=
    (fun _ : ℝ => ((0 : ℝ), c)) +
      fun ε ↦ ε • ((1 : ℝ), (0 : ℝ), (0 : ℝ))
  let inr : (ℝ × ℝ) →L[ℝ] ℝ × (ℝ × ℝ) :=
    ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)
  let derivative : (ℝ × (ℝ × ℝ)) →
      (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ := fderiv ℝ f
  have hpath : HasDerivAt path ((1 : ℝ), (0 : ℝ), (0 : ℝ)) 0 := by
    have hconstant : HasDerivAt (fun _ : ℝ => ((0 : ℝ), c))
        (0 : ℝ × (ℝ × ℝ)) 0 :=
      hasDerivAt_const (0 : ℝ) ((0 : ℝ), c)
    have hscale : HasDerivAt
        (fun t : ℝ => t • ((1 : ℝ), (0 : ℝ), (0 : ℝ)))
        ((1 : ℝ), (0 : ℝ), (0 : ℝ)) 0 := by
      simpa only [id_eq, one_smul] using
        (hasDerivAt_id (0 : ℝ)).smul_const ((1 : ℝ), (0 : ℝ), (0 : ℝ))
    simpa only [path, Pi.add_apply, zero_add] using hconstant.add hscale
  have hderivative : DifferentiableAt ℝ derivative a := by
    have horder : (1 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞) := by
      norm_num
    have hderivContDiff : ContDiffAt ℝ (1 : WithTop ℕ∞)
        (fderiv ℝ f) a := by
      exact hf.contDiffAt.fderiv_right
        (n := (3 : WithTop ℕ∞)) (m := (1 : WithTop ℕ∞)) horder
    exact hderivContDiff.differentiableAt one_ne_zero
  have hderivativeAtPath : HasFDerivAt derivative
      (fderiv ℝ derivative a) (path 0) := by
    simpa only [path, a, Pi.add_apply, zero_smul, add_zero] using
      hderivative.hasFDerivAt
  have hderivativeAlongPath :=
    hderivativeAtPath.comp_hasDerivAt 0 hpath
  let transverseVector : ℝ × (ℝ × ℝ) := inr w
  have htransverseConstant : HasDerivAt (fun _ : ℝ => transverseVector)
      0 0 := hasDerivAt_const (0 : ℝ) transverseVector
  have hpartialDerivative :=
    hderivativeAlongPath.clm_apply htransverseConstant
  have hessianZero :
      (fderiv ℝ (fderiv ℝ f) (0, p, h))
          ((1 : ℝ), (0 : ℝ), (0 : ℝ))
          ((0 : ℝ), w.1, w.2) = 0 := by
    rw [iteratedFDeriv_two_apply] at hzero
    simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using hzero
  have hpartialZero : HasDerivAt
      (fun ε : ℝ => derivative (path ε) transverseVector) 0 0 := by
    apply hpartialDerivative.congr_deriv
    simp only [ContinuousLinearMap.map_zero, add_zero]
    simp only [derivative, a, transverseVector, inr,
      ContinuousLinearMap.inr_apply, c, hessianZero]
  have hanalytic : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      AnalyticAt ℝ f (path ε) := by
    have hpathTendsto : Tendsto path (𝓝 (0 : ℝ)) (𝓝 a) := by
      have hcontinuous : Tendsto path (𝓝 (0 : ℝ)) (𝓝 (path 0)) :=
        hpath.continuousAt
      have hpathZero : path 0 = a := by
        simp only [path, a, Pi.add_apply, zero_smul, add_zero]
      simpa only [hpathZero] using hcontinuous
    exact hpathTendsto.eventually hf.eventually_analyticAt
  have heventuallyEq :
      (fun ε : ℝ =>
        (fderiv ℝ (fun y : ℝ × ℝ => f (ε, y)) c) w) =ᶠ[𝓝 (0 : ℝ)]
        (fun ε : ℝ => derivative (path ε) transverseVector) := by
    filter_upwards [hanalytic] with ε hanalytic
    have hpathPoint : path ε = (ε, c) := by
      simp [path, c, Pi.add_apply]
    have hfunctionDifferentiable : DifferentiableAt ℝ f (ε, c) := by
      rw [← hpathPoint]
      exact hanalytic.differentiableAt
    have htransverseMap : DifferentiableAt ℝ
        (fun y : ℝ × ℝ => (ε, y)) c := by
      fun_prop
    have hcomposition := fderiv_comp c hfunctionDifferentiable htransverseMap
    have htransverseFDeriv :
        fderiv ℝ (fun y : ℝ × ℝ => (ε, y)) c = inr := by
      simpa only [inr] using
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) ε c).fderiv
    have hcompositionApplied := congrArg
      (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L w) hcomposition
    rw [hpathPoint]
    simpa only [derivative, c, transverseVector, Function.comp_def, Function.comp_apply,
      htransverseFDeriv, ContinuousLinearMap.comp_apply] using hcompositionApplied
  exact hpartialZero.congr_of_eventuallyEq heventuallyEq

/-- Helper for Infrastructure I.16a and Lemma 4.15: pointwise zero scale
derivatives after evaluation imply that the first iterated derivative of a
continuous-linear-map-valued scale family is the zero multilinear map. -/
theorem iteratedFDeriv_one_eq_zero_of_apply_scale_hasDerivAt
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (family : ℝ → Y →L[ℝ] ℝ)
    (hregular : ContDiffAt ℝ 1 family 0)
    (happly : ∀ w : Y,
      HasDerivAt (fun ε : ℝ => (family ε) w) 0 0) :
    iteratedFDeriv ℝ 1 family 0 = 0 := by
  apply ContinuousMultilinearMap.ext
  intro direction
  apply ContinuousLinearMap.ext
  intro w
  rw [iteratedFDeriv_one_apply]
  have horder : (1 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hfamily : HasDerivAt family (deriv family 0) 0 := by
    exact hregular.differentiableAt horder |>.hasDerivAt
  have hconstant : HasDerivAt (fun _ : ℝ => w) 0 0 :=
    hasDerivAt_const (0 : ℝ) w
  have hevaluation := hfamily.clm_apply hconstant
  have hzero := happly w
  have hderivativeZero : deriv family 0 w = 0 := by
    have hunique := hevaluation.unique hzero
    simpa only [ContinuousLinearMap.map_zero, add_zero] using hunique
  have hmapOne : (fderiv ℝ family 0) 1 w = 0 := by
    rw [fderiv_apply_one_eq_deriv]
    exact hderivativeZero
  have hdirection : direction 0 = direction 0 • (1 : ℝ) := by
    simp
  rw [hdirection, map_smul]
  simp only [smul_apply, hmapOne, smul_zero, zero_apply]

/-- Helper for Infrastructure I.16a and Lemma 4.15: under analytic positive-slice
data, every fixed transverse direction of the low-gradient derivative family has
zero scale derivative at scale zero. -/
theorem lowGradientTransverseFDerivFamily_apply_scale_hasDerivAt_of_analytic
    (p h : ℝ) (hp : 0 < p) (hh : 0 < h)
    (hf : AnalyticAt ℝ lowGradientFactor (0, p, h)) (w : ℝ × ℝ) :
    HasDerivAt
      (fun ε : ℝ =>
        (lowGradientTransverseFDerivFamily (p, h) ε) w) 0 0 := by
  have hzero := iteratedFDeriv_scale_transverse_eq_zero_at_positive
    lowGradientFactor p h hp hh hf
    (fun p h hp hh => lowGradientFactor_scale_hasDerivAt p h hp hh)
    (0, w.1, w.2) rfl
  simpa only [lowGradientTransverseFDerivFamily, lowGradientFactor] using
    partialFDeriv_apply_hasDerivAt_of_scaleTransverseHessian
      lowGradientFactor p h w hf hzero

/-- Helper for Infrastructure I.16a and Lemma 4.15: the first scale jet of the
low-gradient transverse derivative family vanishes throughout a neighborhood of
the positive transverse base point. -/
theorem lowGradientTransverseFDerivFamily_firstScaleJet_eventually_zero :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 1 (lowGradientTransverseFDerivFamily z) 0 = 0 := by
  have hthreeFinite : (3 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    norm_num
  have hjointEventually : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      ContDiffAt ℝ 3
        (Function.uncurry lowGradientTransverseFDerivFamily) (z, 0) := by
    have hsliceContinuous : ContinuousAt
        (fun z : ℝ × ℝ => (z, (0 : ℝ))) ((2, 1) : ℝ × ℝ) :=
      continuousAt_id.prodMk continuousAt_const
    exact hsliceContinuous.eventually
      (lowGradientTransverseFDerivFamily_contDiffAt.eventually hthreeFinite)
  have hanalyticEventually : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      AnalyticAt ℝ lowGradientFactor (0, z.1, z.2) := by
    have hparameterContinuous : ContinuousAt
        (fun z : ℝ × ℝ => ((0 : ℝ), z.1, z.2)) ((2, 1) : ℝ × ℝ) := by
      fun_prop
    exact hparameterContinuous.eventually
      lowGradientFactor_analyticAt.eventually_analyticAt
  have hpositiveEventually : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      0 < z.1 ∧ 0 < z.2 := by
    have htwoPositive : (0 : ℝ) < 2 := by
      norm_num
    have honePositive : (0 : ℝ) < 1 := by
      norm_num
    have hfirst : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ), 0 < z.1 := by
      exact continuousAt_fst.eventually (Ioi_mem_nhds htwoPositive)
    have hsecond : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ), 0 < z.2 := by
      exact continuousAt_snd.eventually (Ioi_mem_nhds honePositive)
    exact hfirst.and hsecond
  filter_upwards [hjointEventually, hanalyticEventually, hpositiveEventually]
    with z hjoint hanalytic hpositive
  have hregular : ContDiffAt ℝ 1
      (lowGradientTransverseFDerivFamily z) 0 := by
    have horder : (1 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞) := by
      norm_num
    have hsectionMap : ContDiffAt ℝ 1
        (fun r : ℝ => (z, r)) 0 := by
      fun_prop
    have hsection := hjoint.of_le horder |>.comp 0 hsectionMap
    simpa only [Function.uncurry, Function.comp_def, Function.comp_apply] using hsection
  have happly : ∀ w : ℝ × ℝ,
      HasDerivAt
        (fun ε : ℝ => (lowGradientTransverseFDerivFamily z ε) w) 0 0 := by
    intro w
    exact lowGradientTransverseFDerivFamily_apply_scale_hasDerivAt_of_analytic
      z.1 z.2 hpositive.1 hpositive.2 hanalytic w
  exact iteratedFDeriv_one_eq_zero_of_apply_scale_hasDerivAt
    (lowGradientTransverseFDerivFamily z) hregular happly

/-- Helper for Lemma 4.15: after the neighborhood first scale jet is supplied by
the stationarity bridge, the cubic transverse derivative estimate only needs
the corresponding second scale jet. -/
theorem lowGradientFactorTransverseFDeriv_norm_bound_of_secondScaleJet
    (hsecondZero : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2 (lowGradientTransverseFDerivFamily z) 0 = 0) :
    ∃ C > 0, ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ‖fderiv ℝ (fun z : ℝ × ℝ ↦
        (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2)‖ ≤
        C * ‖x.1 ^ (3 : ℕ)‖ := by
  exact lowGradientFactorTransverseFDeriv_norm_bound_of_firstSecondScaleJet
    lowGradientTransverseFDerivFamily_firstScaleJet_eventually_zero hsecondZero

end DFP.SecondLeg
