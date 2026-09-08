module

public import ReasLib.Analysis.Calculus.ContDiff.CrossDerivative
public import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.SlowSecondReduction
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.FirstLegScaleExpansion
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.MixedFlatPath
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.QuotientGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.SlowSecondReduction
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2

/-!
# Intermediate slow-slope germ on the polynomial slow graph

This companion combines the pure-scale first-leg expansion with the flat transverse
slice and proves the corrected seventh-order intermediate-slope remainder.
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg

private lemma firstLegFactorsScale_hasDerivAt (p h : ℝ) :
    HasDerivAt
      (fun ε : ℝ ↦ (DFP.FirstLeg.spectralFactors ε p h,
        DFP.FirstLeg.gradientFactors ε p h))
      ((0, 0), (0, 0)) 0 := by
  let X : ℝ → ℝ := fun ε ↦ ε
  let one : ℝ → ℝ := fun _ ↦ 1
  let two : ℝ → ℝ := fun _ ↦ 2
  let three : ℝ → ℝ := fun _ ↦ 3
  let P : ℝ → ℝ := fun _ ↦ p
  let H : ℝ → ℝ := fun _ ↦ h
  have hX : HasDerivAt X 1 0 := hasDerivAt_id 0
  have hone : HasDerivAt one 0 0 := hasDerivAt_const 0 1
  have htwo : HasDerivAt two 0 0 := hasDerivAt_const 0 2
  have hthree : HasDerivAt three 0 0 := hasDerivAt_const 0 3
  have hP : HasDerivAt P 0 0 := hasDerivAt_const 0 p
  have hH : HasDerivAt H 0 0 := hasDerivAt_const 0 h
  let onePlusCube := one + X ^ 3
  let onePlus := one + X
  have honePlusCube : HasDerivAt onePlusCube 0 0 := by
    exact (hone.add (hX.pow 3)).congr_deriv (g' := 0) (by norm_num)
  have honePlus : HasDerivAt onePlus 1 0 := by
    exact (hone.add hX).congr_deriv (g' := 1) (by norm_num)
  let B := one + ((two * X ^ 3) + X ^ 4)
  have hB : HasDerivAt B 0 0 := by
    exact (hone.add (((htwo.mul (hX.pow 3))).add (hX.pow 4))).congr_deriv
      (g' := 0) (by norm_num)
  let C := onePlusCube ^ 2 + (P * X ^ 6) * onePlus ^ 2
  have hC : HasDerivAt C 0 0 := by
    exact ((honePlusCube.pow 2).add
      ((hP.mul (hX.pow 6)).mul (honePlus.pow 2))).congr_deriv
        (g' := 0) (by norm_num)
  have hB_ne : B 0 ≠ 0 := by norm_num [B, one, two, X]
  have hC_ne : C 0 ≠ 0 := by norm_num [C, onePlusCube, onePlus, one, P, X]
  let a := H * P - (((H * P ^ 2) * X ^ 6) * onePlus ^ 2) / C + one / B
  let b := one / B - ((((H * P) * X ^ 3) * onePlus) * onePlusCube) / C
  let d := H - (H * onePlusCube ^ 2) / C + one / B
  let q := one - (((two * (P + one)) * X ^ 3) * onePlus) / (three * B)
  let v := P - ((two * (P + one)) * onePlusCube) / (three * B)
  have ha : HasDerivAt a 0 0 := by
    exact (((hH.mul hP).sub
      ((((hH.mul (hP.pow 2)).mul (hX.pow 6)).mul (honePlus.pow 2)).div hC hC_ne)).add
        (hone.div hB hB_ne)).congr_deriv (g' := 0)
          (by norm_num [a, B, C, onePlusCube, onePlus, one, two, P, H, X])
  have hb : HasDerivAt b 0 0 := by
    exact ((hone.div hB hB_ne).sub
      (((((hH.mul hP).mul (hX.pow 3)).mul honePlus).mul honePlusCube).div hC hC_ne)).congr_deriv
        (g' := 0)
          (by norm_num [b, B, C, onePlusCube, onePlus, one, two, P, H, X])
  have hd : HasDerivAt d 0 0 := by
    exact ((hH.sub ((hH.mul (honePlusCube.pow 2)).div hC hC_ne)).add
      (hone.div hB hB_ne)).congr_deriv (g' := 0)
        (by norm_num [d, B, C, onePlusCube, one, two, P, H, X])
  have hq : HasDerivAt q 0 0 := by
    exact (hone.sub (((((htwo.mul (hP.add hone)).mul (hX.pow 3)).mul honePlus)).div
      (hthree.mul hB) (by norm_num [B, one, two, three, X]))).congr_deriv
        (g' := 0)
          (by norm_num [q, B, onePlus, one, two, three, P, X])
  have hv : HasDerivAt v 0 0 := by
    exact (hP.sub ((((htwo.mul (hP.add hone)).mul honePlusCube)).div
      (hthree.mul hB) (by norm_num [B, one, two, three, X]))).congr_deriv
        (g' := 0)
          (by norm_num [v, B, onePlusCube, one, two, three, P, X])
  let A := X ^ 4 * a
  let E := X ^ 2 * b
  have hA : HasDerivAt A 0 0 := by
    exact ((hX.pow 4).mul ha).congr_deriv (g' := 0) (by norm_num [A, X])
  have hE : HasDerivAt E 0 0 := by
    exact ((hX.pow 2).mul hb).congr_deriv (g' := 0) (by norm_num [E, X])
  let rad := (d - A) ^ 2 + (fun ε ↦ 4 * (E ^ 2) ε)
  have hrad : HasDerivAt rad 0 0 := by
    exact (((hd.sub hA).pow 2).add ((hE.pow 2).const_mul 4)).congr_deriv
      (g' := 0)
        (by norm_num [rad, d, A, E, a, b, B, C, onePlusCube, onePlus,
          one, two, P, H, X])
  have hrad_ne : rad 0 ≠ 0 := by
    norm_num [rad, d, A, E, a, b, B, C, onePlusCube, onePlus,
      one, two, P, H, X]
  let gap := fun ε ↦ Real.sqrt (rad ε)
  have hgap : HasDerivAt gap 0 0 := by
    exact (hrad.sqrt hrad_ne).congr_deriv (g' := 0)
      (by norm_num [gap, rad, d, A, E, a, b, B, C, onePlusCube,
        onePlus, one, two, P, H, X])
  let high := (A + d + gap) / two
  let low := (A + d - gap) / two
  have hhigh : HasDerivAt high 0 0 := by
    exact (((hA.add hd).add hgap).div htwo (by norm_num [two])).congr_deriv
      (g' := 0) (by norm_num [high, two])
  have hlow : HasDerivAt low 0 0 := by
    exact (((hA.add hd).sub hgap).div htwo (by norm_num [two])).congr_deriv
      (g' := 0) (by norm_num [low, two])
  let denomRad := (d - low) ^ 2 + E ^ 2
  have hdenomRad : HasDerivAt denomRad 0 0 := by
    exact (((hd.sub hlow).pow 2).add (hE.pow 2)).congr_deriv
      (g' := 0)
        (by norm_num [denomRad, d, low, high, gap, rad, A, E, a, b,
          B, C, onePlusCube, onePlus, one, two, P, H, X])
  have hdenomRad_ne : denomRad 0 ≠ 0 := by
    norm_num [denomRad, d, low, high, gap, rad, A, E, a, b,
      B, C, onePlusCube, onePlus, one, two, P, H, X]
  let denom := fun ε ↦ Real.sqrt (denomRad ε)
  have hdenom : HasDerivAt denom 0 0 := by
    exact (hdenomRad.sqrt hdenomRad_ne).congr_deriv (g' := 0)
      (by norm_num [denom, denomRad, d, low, high, gap, rad, A, E, a, b,
        B, C, onePlusCube, onePlus, one, two, P, H, X])
  have hhigh_ne : high 0 ≠ 0 := by
    norm_num [high, gap, rad, d, A, E, a, b, B, C, onePlusCube,
      onePlus, one, two, P, H, X]
  have hdenom_ne : denom 0 ≠ 0 := by
    norm_num [denom, denomRad, d, low, high, gap, rad, A, E, a, b,
      B, C, onePlusCube, onePlus, one, two, P, H, X]
  let spectralLow := (a * d - b ^ 2) / high
  let gradientLow := ((d - low) * q - (X ^ 4 * b) * v) / denom
  let gradientHigh := (b * q + (d - low) * v) / denom
  have hspectralLow : HasDerivAt spectralLow 0 0 := by
    exact (((ha.mul hd).sub (hb.pow 2)).div hhigh hhigh_ne).congr_deriv
      (g' := 0)
        (by norm_num [spectralLow, a, b, d, high, gap, rad, A, E,
          B, C, onePlusCube, onePlus, one, two, P, H, X])
  have hgradientLow : HasDerivAt gradientLow 0 0 := by
    exact ((((hd.sub hlow).mul hq).sub (((hX.pow 4).mul hb).mul hv)).div
      hdenom hdenom_ne).congr_deriv (g' := 0)
        (by norm_num [gradientLow, a, b, d, q, v, low, high, gap, rad,
          A, E, denom, denomRad, B, C, onePlusCube, onePlus, one, two,
          three, P, H, X])
  have hgradientHigh : HasDerivAt gradientHigh 0 0 := by
    exact (((hb.mul hq).add ((hd.sub hlow).mul hv)).div
      hdenom hdenom_ne).congr_deriv (g' := 0)
        (by norm_num [gradientHigh, a, b, d, q, v, low, high, gap, rad,
          A, E, denom, denomRad, B, C, onePlusCube, onePlus, one, two,
          three, P, H, X])
  have hfactorData := (hspectralLow.prodMk hhigh).prodMk
    (hgradientLow.prodMk hgradientHigh)
  apply hfactorData.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun ε ↦ by
    simp [DFP.FirstLeg.spectralFactors, DFP.FirstLeg.gradientFactors,
      RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap,
      RealSymmetric2.lowDenom, spectralLow, gradientLow, gradientHigh, denom,
      denomRad, low, high, gap, rad, A, E, a, b, d, q, v, B, C,
      onePlusCube, onePlus, one, two, three, P, H, X]
    ring_nf
    simp)

private theorem iteratedFDeriv_scale_transverse_eq_zero
    (f : (ℝ × ℝ × ℝ) → ℝ)
    (hf : AnalyticAt ℝ f (0, 2, 1))
    (hscale : ∀ p h : ℝ, 0 < p → 0 < h →
      HasDerivAt (fun ε : ℝ ↦ f (ε, p, h)) 0 0)
    (v : ℝ × ℝ × ℝ) (hv : v.1 = 0) :
    iteratedFDeriv ℝ 2 f (0, 2, 1)
      ![((1, 0, 0) : ℝ × ℝ × ℝ), v] = 0 := by
  let a : ℝ × ℝ × ℝ := (0, 2, 1)
  let u : ℝ × ℝ × ℝ := (1, 0, 0)
  let line : ℝ → ℝ × ℝ × ℝ := fun t ↦ a + t • v
  have hline : Tendsto line (𝓝 0) (𝓝 a) := by
    have hc : ContinuousAt line 0 := by
      dsimp only [line]
      fun_prop
    have hline_zero : line 0 = a := by simp [line]
    rw [← hline_zero]
    exact hc
  have hanalytic : ∀ᶠ t in 𝓝 (0 : ℝ), AnalyticAt ℝ f (line t) :=
    hline.eventually hf.eventually_analyticAt
  have hp_nhds : ∀ᶠ x in 𝓝 a, 0 < x.2.1 := by
    have hc : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.1) a := by fun_prop
    apply hc.eventually
    exact Ioi_mem_nhds (by norm_num [a])
  have hh_nhds : ∀ᶠ x in 𝓝 a, 0 < x.2.2 := by
    have hc : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.2) a := by fun_prop
    apply hc.eventually
    exact Ioi_mem_nhds (by norm_num [a])
  have hp_line : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (line t).2.1 :=
    hline.eventually hp_nhds
  have hh_line : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (line t).2.2 :=
    hline.eventually hh_nhds
  have hzero : ∀ᶠ t in 𝓝 (0 : ℝ),
      fderiv ℝ f (a + t • v) u = 0 := by
    filter_upwards [hanalytic, hp_line, hh_line] with t hft hpt hht
    let x : ℝ × ℝ × ℝ := line t
    have hx_scale : x.1 = 0 := by
      simp [x, line, a, hv]
    have hx_eq : ((0, x.2.1, x.2.2) : ℝ × ℝ × ℝ) = x := by
      ext <;> simp [hx_scale]
    have hinner : HasDerivAt
        (fun ε : ℝ ↦ ((ε, x.2.1, x.2.2) : ℝ × ℝ × ℝ)) u 0 := by
      have hpconst : HasDerivAt (fun _ : ℝ ↦ x.2.1) 0 0 :=
        hasDerivAt_const 0 x.2.1
      have hhconst : HasDerivAt (fun _ : ℝ ↦ x.2.2) 0 0 :=
        hasDerivAt_const 0 x.2.2
      simpa only [u, id_eq] using (hasDerivAt_id (0 : ℝ)).prodMk
        (hpconst.prodMk hhconst)
    have hft' : DifferentiableAt ℝ f ((0, x.2.1, x.2.2) : ℝ × ℝ × ℝ) := by
      simpa only [hx_eq] using hft.differentiableAt
    have hchain := hft'.hasFDerivAt.comp_hasDerivAt 0 hinner
    have hstationary := hscale x.2.1 x.2.2 hpt hht
    have hvalue :
        fderiv ℝ f ((0, x.2.1, x.2.2) : ℝ × ℝ × ℝ) u = 0 :=
      hchain.unique hstationary
    change fderiv ℝ f x u = 0
    simpa only [hx_eq] using hvalue
  have hf2 : ContDiffAt ℝ 2 f (0, 2, 1) := hf.contDiffAt
  simpa only [a, u] using
    hf2.iteratedFDeriv_two_apply_eq_zero_of_eventually_fderiv_line_eq_zero
      ((1, 0, 0) : ℝ × ℝ × ℝ) v (by simpa only [a, u] using hzero)

end DFP.TwoLeg

namespace DFP.TwoLeg.EndpointAngleJet


private theorem firstLeg_gradientFactors_zero (p h : ℝ) :
    DFP.FirstLeg.gradientFactors 0 p h = (1, (p + 1) / 3) := by
  norm_num [DFP.FirstLeg.gradientFactors, RealSymmetric2.low,
    RealSymmetric2.gap, RealSymmetric2.lowDenom]
  ring

private theorem firstLeg_gradientFactor_scale_hasDerivAt_fst (p h : ℝ) :
    HasDerivAt (fun ε : ℝ ↦ (DFP.FirstLeg.gradientFactors ε p h).1) 0 0 := by
  have hgradient : HasDerivAt
      (fun ε : ℝ ↦ DFP.FirstLeg.gradientFactors ε p h) (0, 0) 0 := by
    simpa using
      (DFP.TwoLeg.firstLegFactorsScale_hasDerivAt p h).hasFDerivAt.snd.hasDerivAt
  simpa using hgradient.hasFDerivAt.fst.hasDerivAt

private theorem firstLeg_gradientFactor_scale_hasDerivAt_snd (p h : ℝ) :
    HasDerivAt (fun ε : ℝ ↦ (DFP.FirstLeg.gradientFactors ε p h).2) 0 0 := by
  have hgradient : HasDerivAt
      (fun ε : ℝ ↦ DFP.FirstLeg.gradientFactors ε p h) (0, 0) 0 := by
    simpa using
      (DFP.TwoLeg.firstLegFactorsScale_hasDerivAt p h).hasFDerivAt.snd.hasDerivAt
  simpa using hgradient.hasFDerivAt.snd.hasDerivAt

private theorem gradientFactor_fst_scale_transverse_cross_eq_zero
    (v : ℝ × ℝ × ℝ) (hv : v.1 = 0) :
    iteratedFDeriv ℝ 2
        (fun x : ℝ × ℝ × ℝ ↦
          (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1)
        (0, 2, 1) ![((1, 0, 0) : ℝ × ℝ × ℝ), v] = 0 := by
  have hf : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦
        (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1) (0, 2, 1) := by
    exact analyticAt_fst.comp
      ((analyticAt_fst.comp analyticAt_snd).comp DFP.FirstLeg.factorsAnalytic)
  refine DFP.TwoLeg.iteratedFDeriv_scale_transverse_eq_zero _ hf ?_ v hv
  intro p h _ _
  exact firstLeg_gradientFactor_scale_hasDerivAt_fst p h

private theorem gradientFactor_snd_scale_transverse_cross_eq_zero
    (v : ℝ × ℝ × ℝ) (hv : v.1 = 0) :
    iteratedFDeriv ℝ 2
        (fun x : ℝ × ℝ × ℝ ↦
          (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2)
        (0, 2, 1) ![((1, 0, 0) : ℝ × ℝ × ℝ), v] = 0 := by
  have hf : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦
        (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2) (0, 2, 1) := by
    exact analyticAt_snd.comp
      ((analyticAt_fst.comp analyticAt_snd).comp DFP.FirstLeg.factorsAnalytic)
  refine DFP.TwoLeg.iteratedFDeriv_scale_transverse_eq_zero _ hf ?_ v hv
  intro p h _ _
  exact firstLeg_gradientFactor_scale_hasDerivAt_snd p h

end DFP.TwoLeg.EndpointAngleJet
namespace DFP.TwoLeg.EndpointAngleJet

/-- The first-leg gradient factors along the polynomial slow graph have the
displayed order-five germs. -/
theorem slowFirstLegGradientFactors_eqModPow_five :
    DFP.TwoLeg.EqModPow 5
        (fun ε : ℝ ↦
          (DFP.FirstLeg.gradientFactors
            (DFP.TwoLeg.slowGraphJetPath ε).1
            (DFP.TwoLeg.slowGraphJetPath ε).2.1
            (DFP.TwoLeg.slowGraphJetPath ε).2.2).1)
        (fun ε : ℝ ↦ 1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4) ∧
      DFP.TwoLeg.EqModPow 5
        (fun ε : ℝ ↦
          (DFP.FirstLeg.gradientFactors
            (DFP.TwoLeg.slowGraphJetPath ε).1
            (DFP.TwoLeg.slowGraphJetPath ε).2.1
            (DFP.TwoLeg.slowGraphJetPath ε).2.2).2)
        (fun ε : ℝ ↦ 1 + (56 / 5) * ε ^ 3 - (11 / 10) * ε ^ 4) := by
  let Q : (ℝ × ℝ × ℝ) → ℝ := fun x ↦
    (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1
  let U : (ℝ × ℝ × ℝ) → ℝ := fun x ↦
    (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2
  let a : ℝ × ℝ × ℝ := (0, 2, 1)
  let u : ℝ × ℝ × ℝ := (1, 0, 0)
  let v₃ : ℝ × ℝ × ℝ := (0, 198 / 5, 8)
  let v₄ : ℝ × ℝ × ℝ := (0, -9 / 5, 0)
  let full : ℝ → ℝ × ℝ × ℝ := fun ε ↦
    (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
      1 + 8 * ε ^ 3)
  let pure : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, 2, 1)
  let flat : ℝ → ℝ × ℝ × ℝ := fun ε ↦
    (0, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
      1 + 8 * ε ^ 3)
  let QP : ℝ → ℝ := fun ε ↦ 1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4
  let UP : ℝ → ℝ := fun ε ↦ 1 - 2 * ε ^ 3 - (1 / 2) * ε ^ 4
  let QflatP : ℝ → ℝ := fun _ ↦ 1
  let UflatP : ℝ → ℝ := fun ε ↦
    1 + (66 / 5) * ε ^ 3 - (3 / 5) * ε ^ 4
  have hgradient : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦
        DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2) a := by
    have hgradientBase : AnalyticAt ℝ
        (fun x : ℝ × ℝ × ℝ ↦
          DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2) (0, 2, 1) := by
      apply ((analyticAt_fst.comp analyticAt_snd).comp
        DFP.FirstLeg.factorsAnalytic).congr
      filter_upwards [] with x
      rfl
    simpa only [a] using hgradientBase
  have hQanalytic : AnalyticAt ℝ Q a := analyticAt_fst.comp hgradient
  have hUanalytic : AnalyticAt ℝ U a := analyticAt_snd.comp hgradient
  have hQmixedRaw := FiniteTaylorJet.analytic_mixed_cubic_quartic_isBigO
    Q a u v₃ v₄ hQanalytic
      (gradientFactor_fst_scale_transverse_cross_eq_zero v₃ (by rfl))
  have hUmixedRaw := FiniteTaylorJet.analytic_mixed_cubic_quartic_isBigO
    U a u v₃ v₄ hUanalytic
      (gradientFactor_snd_scale_transverse_cross_eq_zero v₃ (by rfl))
  have hQmixed : DFP.TwoLeg.EqModPow 5 (fun ε ↦ Q (full ε))
      (fun ε ↦ Q (pure ε) + Q (flat ε) - 1) := by
    apply DFP.TwoLeg.EqModPow.of_isBigO
    refine hQmixedRaw.congr' ?_ (Filter.Eventually.of_forall fun _ ↦ rfl)
    exact Filter.Eventually.of_forall (fun ε ↦ by
      dsimp [a, u, v₃, v₄, full, pure, flat, Q]
      ring_nf
      rw [firstLeg_gradientFactors_zero, firstLeg_gradientFactors_zero]
      ring)
  have hUmixed : DFP.TwoLeg.EqModPow 5 (fun ε ↦ U (full ε))
      (fun ε ↦ U (pure ε) + U (flat ε) - 1) := by
    apply DFP.TwoLeg.EqModPow.of_isBigO
    refine hUmixedRaw.congr' ?_ (Filter.Eventually.of_forall fun _ ↦ rfl)
    exact Filter.Eventually.of_forall (fun ε ↦ by
      dsimp [a, u, v₃, v₄, full, pure, flat, U]
      ring_nf
      rw [firstLeg_gradientFactors_zero, firstLeg_gradientFactors_zero]
      ring)
  have hQpure : DFP.TwoLeg.EqModPow 5 (fun ε ↦ Q (pure ε)) QP := by
    simpa only [Q, pure, QP] using
      DFP.TwoLeg.firstLeg_scale_factor_expansions.2.2.1
  have hUpure : DFP.TwoLeg.EqModPow 5 (fun ε ↦ U (pure ε)) UP := by
    simpa only [U, pure, UP] using
      DFP.TwoLeg.firstLeg_scale_factor_expansions.2.2.2
  have hQflat : DFP.TwoLeg.EqModPow 5 (fun ε ↦ Q (flat ε)) QflatP := by
    apply DFP.TwoLeg.EqModPow.of_eq 5
    intro ε
    dsimp only [Q, flat, QflatP]
    rw [firstLeg_gradientFactors_zero]
  have hUflat : DFP.TwoLeg.EqModPow 5 (fun ε ↦ U (flat ε)) UflatP := by
    apply DFP.TwoLeg.EqModPow.of_eq 5
    intro ε
    dsimp only [U, flat, UflatP]
    rw [firstLeg_gradientFactors_zero]
    dsimp
    ring
  have hQassembled := (hQpure.add hQflat).sub
    (DFP.TwoLeg.EqModPow.refl 5 (fun _ : ℝ ↦ (1 : ℝ)))
  have hUassembled := (hUpure.add hUflat).sub
    (DFP.TwoLeg.EqModPow.refl 5 (fun _ : ℝ ↦ (1 : ℝ)))
  constructor
  · have h := hQmixed.trans hQassembled
    exact DFP.TwoLeg.EqModPow.congr h
      (fun ε ↦ by simp only [full, Q, DFP.TwoLeg.slowGraphJetPath_apply])
      (fun ε ↦ by dsimp only [QP, QflatP]; ring)
  · have h := hUmixed.trans hUassembled
    exact DFP.TwoLeg.EqModPow.congr h
      (fun ε ↦ by simp only [full, U, DFP.TwoLeg.slowGraphJetPath_apply])
      (fun ε ↦ by dsimp only [UP, UflatP]; ring)

end DFP.TwoLeg.EndpointAngleJet
namespace DFP.TwoLeg.EndpointAngleJet

/-- The corrected sixth-order polynomial captures the intermediate slow-graph
slope with a seventh-order remainder. -/
theorem slowIntermediateSlope_remainder :
    (fun ε : ℝ ↦ slowIntermediateSlope ε -
      slowIntermediateSlopePolynomial ε) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) := by
  let Q : ℝ → ℝ := fun ε ↦
    (DFP.FirstLeg.gradientFactors
      (DFP.TwoLeg.slowGraphJetPath ε).1
      (DFP.TwoLeg.slowGraphJetPath ε).2.1
      (DFP.TwoLeg.slowGraphJetPath ε).2.2).1
  let U : ℝ → ℝ := fun ε ↦
    (DFP.FirstLeg.gradientFactors
      (DFP.TwoLeg.slowGraphJetPath ε).1
      (DFP.TwoLeg.slowGraphJetPath ε).2.1
      (DFP.TwoLeg.slowGraphJetPath ε).2.2).2
  let QP : ℝ → ℝ := fun ε ↦ 1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4
  let UP : ℝ → ℝ := fun ε ↦
    1 + (56 / 5) * ε ^ 3 - (11 / 10) * ε ^ 4
  let R : ℝ → ℝ := fun ε ↦ 1 + (66 / 5) * ε ^ 3 + (7 / 5) * ε ^ 4
  rcases slowFirstLegGradientFactors_eqModPow_five with ⟨hQraw, hUraw⟩
  have hQ : DFP.TwoLeg.EqModPow 5 Q QP := by
    simpa only [Q, QP] using hQraw
  have hU : DFP.TwoLeg.EqModPow 5 U UP := by
    simpa only [U, UP] using hUraw
  have hpoly : DFP.TwoLeg.EqModPow 5 UP (fun ε ↦ QP ε * R ε) := by
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (132 / 5) * ε + (179 / 5) * ε ^ 2 + (7 / 2) * ε ^ 3)
    · fun_prop
    · intro ε
      dsimp only [UP, QP, R]
      ring
  have hQPcont : ContinuousAt QP 0 := by
    dsimp only [QP]
    fun_prop
  have hRcont : ContinuousAt R 0 := by
    dsimp only [R]
    fun_prop
  have hpath : ContinuousAt DFP.TwoLeg.slowGraphJetPath 0 := by
    unfold DFP.TwoLeg.slowGraphJetPath DFP.TwoLeg.graphJetPath
    fun_prop
  have hpathZero :
      DFP.TwoLeg.slowGraphJetPath 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    norm_num [DFP.TwoLeg.slowGraphJetPath, DFP.TwoLeg.graphJetPath]
  have hgradient : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦
        DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2) (0, 2, 1) := by
    apply ((analyticAt_fst.comp analyticAt_snd).comp
      DFP.FirstLeg.factorsAnalytic).congr
    filter_upwards [] with x
    rfl
  have hQouter : ContinuousAt
      (fun x : ℝ × ℝ × ℝ ↦
        (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1)
      (DFP.TwoLeg.slowGraphJetPath 0) := by
    rw [hpathZero]
    exact (analyticAt_fst.comp hgradient).continuousAt
  have hQcont : ContinuousAt Q 0 := by
    exact hQouter.comp hpath
  have hQzero : Q 0 ≠ 0 := by
    dsimp only [Q]
    rw [hpathZero, firstLeg_gradientFactors_zero]
    norm_num
  have hRatio : DFP.TwoLeg.EqModPow 5 (fun ε ↦ U ε / Q ε) R :=
    DFP.TwoLeg.EqModPow.div_approx hU hQ hpoly hQPcont hRcont hQcont hQzero
  have hScaled := hRatio.mul_pow_left (k := 2)
  have hSlope : DFP.TwoLeg.EqModPow 7 slowIntermediateSlope
      slowIntermediateSlopePolynomial := by
    apply DFP.TwoLeg.EqModPow.congr hScaled
    · intro ε
      dsimp only [slowIntermediateSlope, Q, U]
      ring
    · intro ε
      dsimp only [slowIntermediateSlopePolynomial, R]
      ring
  exact hSlope.to_isBigO

end DFP.TwoLeg.EndpointAngleJet


