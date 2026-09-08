module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FrameAngleJet
import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.Smoothness
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import all ReasLib.Geometry.Euclidean.Plane.SignedAngle

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

noncomputable section

/-- A smooth scalar observable preserves fifth-order closeness to the polynomial
slow-graph path. -/
private theorem smoothFrameSlopeStabilityUnderGraphJets
    (F : ℝ × ℝ × ℝ → ℝ)
    (hF : ContDiffAt ℝ 1 F ((0, 2, 1) : ℝ × ℝ × ℝ))
    (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦ F (ε, p ε, h ε) - F (slowGraphJetPath ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  let x : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p ε, h ε)
  let x₀ : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p₀ ε, h₀ ε)
  have hpDiff : (fun ε ↦ p ε - p₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀] using h_pJet
  have hhDiff : (fun ε ↦ h ε - h₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀] using h_hJet
  have hpowFiveTendsto : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    have hp₀Tendsto : Tendsto p₀ (𝓝 0) (𝓝 2) := by
      have hcontinuous : ContinuousAt p₀ 0 := by
        dsimp only [p₀]
        fun_prop
      convert hcontinuous.tendsto using 1
      norm_num [p₀]
    simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpowFiveTendsto).add hp₀Tendsto
  have hhTendsto : Tendsto h (𝓝 0) (𝓝 1) := by
    have hh₀Tendsto : Tendsto h₀ (𝓝 0) (𝓝 1) := by
      have hcontinuous : ContinuousAt h₀ 0 := by
        dsimp only [h₀]
        fun_prop
      convert hcontinuous.tendsto using 1
      norm_num [h₀]
    simpa only [sub_add_cancel, zero_add] using
      (hhDiff.trans_tendsto hpowFiveTendsto).add hh₀Tendsto
  have hxTendsto : Tendsto x (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [x, id_eq, nhds_prod_eq] using
      tendsto_id.prodMk (hpTendsto.prodMk hhTendsto)
  have hx₀Tendsto : Tendsto x₀ (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    have hcontinuous : ContinuousAt x₀ 0 := by
      dsimp only [x₀, p₀, h₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [x₀, p₀, h₀]
  have hpathDiff : (fun ε ↦ x ε - x₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) :=
      Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
    simpa [x, x₀] using hzero.prod_left (hpDiff.prod_left hhDiff)
  have houter := hF.hasStrictFDerivAt one_ne_zero |>.isBigO_sub
  have hpairs : Tendsto (fun ε ↦ (x ε, x₀ ε)) (𝓝 0)
      (𝓝 (((0, 2, 1), (0, 2, 1)) :
        (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ))) := by
    simpa only [nhds_prod_eq] using hxTendsto.prodMk hx₀Tendsto
  have hcomposed := houter.comp_tendsto hpairs
  have hcomposed' : (fun ε ↦ F (x ε) - F (x₀ ε)) =O[𝓝 0]
      (fun ε ↦ x ε - x₀ ε) := by
    simpa only [Function.comp_def] using hcomposed
  have hstability := hcomposed'.trans hpathDiff
  simpa only [x, x₀, p₀, h₀, slowGraphJetPath_apply] using hstability

/-- The first-leg metric off-diagonal entry after removing its explicit factor
`ε ^ 2`. -/
private def firstFrameOffDiagonalResidual (x : ℝ × ℝ × ℝ) : ℝ :=
  let ε := x.1
  let p := x.2.1
  let h := x.2.2
  let B := 1 + 2 * ε ^ 3 + ε ^ 4
  let C := (1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2
  1 / B - h * p * ε ^ 3 * (1 + ε) * (1 + ε ^ 3) / C

/-- The second-leg metric off-diagonal entry after removing its explicit factor
`ε ^ 2`. -/
private def secondFrameOffDiagonalResidual (x : ℝ × ℝ × ℝ) : ℝ :=
  let ε := x.1
  let spectral := DFP.FirstLeg.spectralFactors ε x.2.1 x.2.2
  let gradient := DFP.FirstLeg.gradientFactors ε x.2.1 x.2.2
  let L := spectral.1
  let H := spectral.2
  let Q := gradient.1
  let U := gradient.2
  let w₁ := ε * L * Q - 2 * H * U
  let w₂ := H * U - 2 * ε ^ 3 * L * Q
  let beta := ε ^ 3 * L * Q * w₁ + H * U * w₂
  let gamma := ε ^ 6 * L * w₁ ^ 2 + H * w₂ ^ 2
  (-(ε ^ 3 * L * H * w₁ * w₂ / gamma) + L * Q * H * U / beta)

/-- The smooth first-leg frame tilt obtained after removing the transverse factor
`ε ^ 2`. -/
private def firstFrameTiltFactor (x : ℝ × ℝ × ℝ) : ℝ :=
  let ε := x.1
  let p := x.2.1
  let h := x.2.2
  let H := DFP.FirstLeg.outputMetric ε p h
  (-firstFrameOffDiagonalResidual x * DFP.FirstLeg.frame ε p h 0 0 /
    (H 1 1 - RealSymmetric2.low (H 0 0) (H 0 1) (H 1 1)))

/-- The smooth second-leg frame tilt obtained after removing the transverse factor
`ε ^ 2`. -/
private def secondFrameTiltFactor (x : ℝ × ℝ × ℝ) : ℝ :=
  let ε := x.1
  let p := x.2.1
  let h := x.2.2
  let H := DFP.SecondLeg.outputMetric ε p h
  (-secondFrameOffDiagonalResidual x * DFP.SecondLeg.frame ε p h 0 0 /
    (H 1 1 - RealSymmetric2.low (H 0 0) (H 0 1) (H 1 1)))

/-- The normalized first-leg off-diagonal residual is analytic at the canceled base
state. -/
private theorem firstFrameOffDiagonalResidual_analyticAt :
    AnalyticAt ℝ firstFrameOffDiagonalResidual (0, 2, 1) := by
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) :=
    analyticAt_fst
  have hp : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.2.1) (0, 2, 1) :=
    analyticAt_fst.comp analyticAt_snd
  have hh : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.2.2) (0, 2, 1) :=
    analyticAt_snd.comp analyticAt_snd
  let B : ℝ × ℝ × ℝ → ℝ := fun x ↦ 1 + 2 * x.1 ^ 3 + x.1 ^ 4
  let C : ℝ × ℝ × ℝ → ℝ := fun x ↦
    (1 + x.1 ^ 3) ^ 2 + x.2.1 * x.1 ^ 6 * (1 + x.1) ^ 2
  have hB : AnalyticAt ℝ B (0, 2, 1) := by
    dsimp only [B]
    fun_prop
  have hC : AnalyticAt ℝ C (0, 2, 1) := by
    dsimp only [C]
    fun_prop
  have hBne : B (0, 2, 1) ≠ 0 := by
    norm_num [B]
  have hCne : C (0, 2, 1) ≠ 0 := by
    norm_num [C]
  have hone : AnalyticAt ℝ (fun _ : ℝ × ℝ × ℝ ↦ (1 : ℝ)) (0, 2, 1) :=
    analyticAt_const
  have honePlusEpsilon : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ 1 + x.1) (0, 2, 1) :=
    hone.add hε
  have honePlusCube : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ 1 + x.1 ^ 3) (0, 2, 1) :=
    hone.add (hε.pow 3)
  have hnumerator :=
    (((((hh.mul hp).mul (hε.pow 3)).mul honePlusEpsilon).mul honePlusCube))
  have hformula := (hone.div hB hBne).sub (hnumerator.div hC hCne)
  apply hformula.congr
  filter_upwards [] with x
  rfl

/-- The normalized second-leg off-diagonal residual is analytic at the canceled base
state. -/
private theorem secondFrameOffDiagonalResidual_analyticAt :
    AnalyticAt ℝ secondFrameOffDiagonalResidual (0, 2, 1) := by
  let L : ℝ × ℝ × ℝ → ℝ := fun x ↦
    (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1
  let H : ℝ × ℝ × ℝ → ℝ := fun x ↦
    (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2
  let Q : ℝ × ℝ × ℝ → ℝ := fun x ↦
    (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1
  let U : ℝ × ℝ × ℝ → ℝ := fun x ↦
    (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2
  let w₁ : ℝ × ℝ × ℝ → ℝ := fun x ↦
    x.1 * L x * Q x - 2 * H x * U x
  let w₂ : ℝ × ℝ × ℝ → ℝ := fun x ↦
    H x * U x - 2 * x.1 ^ 3 * L x * Q x
  let beta : ℝ × ℝ × ℝ → ℝ := fun x ↦
    x.1 ^ 3 * L x * Q x * w₁ x + H x * U x * w₂ x
  let gamma : ℝ × ℝ × ℝ → ℝ := fun x ↦
    x.1 ^ 6 * L x * w₁ x ^ 2 + H x * w₂ x ^ 2
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) :=
    analyticAt_fst
  have hspectral : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦
        DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2) (0, 2, 1) :=
    analyticAt_fst.comp DFP.FirstLeg.factorsAnalytic
  have hgradient : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦
        DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2) (0, 2, 1) :=
    (analyticAt_fst.comp analyticAt_snd).comp DFP.FirstLeg.factorsAnalytic
  have hL : AnalyticAt ℝ L (0, 2, 1) := by
    have hraw := analyticAt_fst.comp hspectral
    apply hraw.congr
    filter_upwards [] with x
    rfl
  have hH : AnalyticAt ℝ H (0, 2, 1) := by
    have hraw := analyticAt_snd.comp hspectral
    apply hraw.congr
    filter_upwards [] with x
    rfl
  have hQ : AnalyticAt ℝ Q (0, 2, 1) := by
    have hraw := analyticAt_fst.comp hgradient
    apply hraw.congr
    filter_upwards [] with x
    rfl
  have hU : AnalyticAt ℝ U (0, 2, 1) := by
    have hraw := analyticAt_snd.comp hgradient
    apply hraw.congr
    filter_upwards [] with x
    rfl
  have htwo : AnalyticAt ℝ (fun _ : ℝ × ℝ × ℝ ↦ (2 : ℝ)) (0, 2, 1) :=
    analyticAt_const
  have hw₁ : AnalyticAt ℝ w₁ (0, 2, 1) := by
    dsimp only [w₁]
    exact ((hε.mul hL).mul hQ).sub ((htwo.mul hH).mul hU)
  have hw₂ : AnalyticAt ℝ w₂ (0, 2, 1) := by
    dsimp only [w₂]
    exact (hH.mul hU).sub (((htwo.mul (hε.pow 3)).mul hL).mul hQ)
  have hbeta : AnalyticAt ℝ beta (0, 2, 1) := by
    dsimp only [beta]
    exact ((((hε.pow 3).mul hL).mul hQ).mul hw₁).add
      ((hH.mul hU).mul hw₂)
  have hgamma : AnalyticAt ℝ gamma (0, 2, 1) := by
    dsimp only [gamma]
    exact (((hε.pow 6).mul hL).mul (hw₁.pow 2)).add (hH.mul (hw₂.pow 2))
  have hspectralBase : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradientBase : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  have hbetaNe : beta (0, 2, 1) ≠ 0 := by
    norm_num [beta, w₁, w₂, L, H, Q, U, hspectralBase, hgradientBase]
  have hgammaNe : gamma (0, 2, 1) ≠ 0 := by
    norm_num [gamma, w₁, w₂, L, H, Q, U, hspectralBase, hgradientBase]
  have hfirst := (((((hε.pow 3).mul hL).mul hH).mul hw₁).mul hw₂).div
    hgamma hgammaNe
  have hsecond := (((hL.mul hQ).mul hH).mul hU).div hbeta hbetaNe
  have hformula := hfirst.neg.add hsecond
  apply hformula.congr
  filter_upwards [] with x
  rfl

/-- The first-leg frame tilt remaining after removal of `ε ^ 2` is analytic at the
canceled base state. -/
private theorem firstFrameTiltFactor_analyticAt :
    AnalyticAt ℝ firstFrameTiltFactor (0, 2, 1) := by
  let entries : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun x ↦
    (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0,
      DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1,
      DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1)
  have hzero := DFP.FirstLeg.outputMetricEntry_analyticAt 0 0
  have hone := DFP.FirstLeg.outputMetricEntry_analyticAt 0 1
  have htwo := DFP.FirstLeg.outputMetricEntry_analyticAt 1 1
  have hentries : AnalyticAt ℝ entries (0, 2, 1) := by
    exact hzero.prod (hone.prod htwo)
  have hentriesBase : entries (0, 2, 1) = ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    norm_num [entries, DFP.FirstLeg.outputMetric]
  have hlowOuter := RealSymmetric2.analyticOnNhd_low
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  rw [← hentriesBase] at hlowOuter
  have hlowComposed := hlowOuter.comp hentries
  have hlow : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦
        let H := DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2
        RealSymmetric2.low (H 0 0) (H 0 1) (H 1 1)) (0, 2, 1) := by
    apply hlowComposed.congr
    filter_upwards [] with x
    rfl
  have hgap := htwo.sub hlow
  have hgapNe :
      DFP.FirstLeg.outputMetric 0 2 1 1 1 -
        RealSymmetric2.low (DFP.FirstLeg.outputMetric 0 2 1 0 0)
          (DFP.FirstLeg.outputMetric 0 2 1 0 1)
          (DFP.FirstLeg.outputMetric 0 2 1 1 1) ≠ 0 := by
    norm_num [DFP.FirstLeg.outputMetric, RealSymmetric2.low, RealSymmetric2.gap]
  have hframe := DFP.FirstLeg.frameEntry_analyticAt 0 0
  have hformula :=
    (firstFrameOffDiagonalResidual_analyticAt.neg.mul hframe).div hgap hgapNe
  apply hformula.congr
  filter_upwards [] with x
  rfl

/-- The second-leg frame tilt remaining after removal of `ε ^ 2` is analytic at the
canceled base state. -/
private theorem secondFrameTiltFactor_analyticAt :
    AnalyticAt ℝ secondFrameTiltFactor (0, 2, 1) := by
  let entries : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun x ↦
    (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 0,
      DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 1,
      DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 1 1)
  have hzero := DFP.SecondLeg.outputMetricEntry_analyticAt 0 0
  have hone := DFP.SecondLeg.outputMetricEntry_analyticAt 0 1
  have htwo := DFP.SecondLeg.outputMetricEntry_analyticAt 1 1
  have hentries : AnalyticAt ℝ entries (0, 2, 1) := by
    exact hzero.prod (hone.prod htwo)
  have hspectralBase : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradientBase : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  have hentriesBase : entries (0, 2, 1) = ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    norm_num [entries, DFP.SecondLeg.outputMetric, hspectralBase, hgradientBase]
  have hlowOuter := RealSymmetric2.analyticOnNhd_low
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  rw [← hentriesBase] at hlowOuter
  have hlowComposed := hlowOuter.comp hentries
  have hlow : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦
        let H := DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2
        RealSymmetric2.low (H 0 0) (H 0 1) (H 1 1)) (0, 2, 1) := by
    apply hlowComposed.congr
    filter_upwards [] with x
    rfl
  have hgap := htwo.sub hlow
  have hgapNe :
      DFP.SecondLeg.outputMetric 0 2 1 1 1 -
        RealSymmetric2.low (DFP.SecondLeg.outputMetric 0 2 1 0 0)
          (DFP.SecondLeg.outputMetric 0 2 1 0 1)
          (DFP.SecondLeg.outputMetric 0 2 1 1 1) ≠ 0 := by
    norm_num [DFP.SecondLeg.outputMetric, hspectralBase, hgradientBase,
      RealSymmetric2.low, RealSymmetric2.gap]
  have hframe := DFP.SecondLeg.frameEntry_analyticAt 0 0
  have hformula :=
    (secondFrameOffDiagonalResidual_analyticAt.neg.mul hframe).div hgap hgapNe
  apply hformula.congr
  filter_upwards [] with x
  rfl

/-- The first-leg metric off-diagonal entry is `ε ^ 2` times its normalized residual. -/
private theorem firstOutputMetric_offDiagonal_eq (x : ℝ × ℝ × ℝ) :
    DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1 =
      x.1 ^ 2 * firstFrameOffDiagonalResidual x := by
  rcases x with ⟨ε, p, h⟩
  rfl

/-- The second-leg metric off-diagonal entry is `ε ^ 2` times its normalized residual. -/
private theorem secondOutputMetric_offDiagonal_eq (x : ℝ × ℝ × ℝ) :
    DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 1 =
      x.1 ^ 2 * secondFrameOffDiagonalResidual x := by
  rcases x with ⟨ε, p, h⟩
  rfl

/-- Away from the nonzero low-eigenvector gap, the first frame tilt carries an exact
factor `ε ^ 2`. -/
private theorem firstFrame_transverse_eq (x : ℝ × ℝ × ℝ)
    (hgap :
      DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1 -
        RealSymmetric2.low
          (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
          (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
          (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1) ≠ 0) :
    DFP.FirstLeg.frame x.1 x.2.1 x.2.2 1 0 =
      x.1 ^ 2 * firstFrameTiltFactor x := by
  unfold DFP.FirstLeg.frame
  simp only [EuclideanPlane.frame, Matrix.cons_val_zero,
    RealSymmetric2.lowVector, PiLp.smul_apply, RealSymmetric2.lowRaw,
    Matrix.cons_val_one, smul_eq_mul]
  rw [firstOutputMetric_offDiagonal_eq]
  rw [firstOutputMetric_offDiagonal_eq] at hgap
  unfold firstFrameTiltFactor
  unfold DFP.FirstLeg.frame
  simp only [EuclideanPlane.frame, Matrix.cons_val_zero,
    RealSymmetric2.lowVector, PiLp.smul_apply, RealSymmetric2.lowRaw,
    smul_eq_mul]
  rw [firstOutputMetric_offDiagonal_eq]
  field_simp [hgap]

/-- Away from the nonzero low-eigenvector gap, the second frame tilt carries an exact
factor `ε ^ 2`. -/
private theorem secondFrame_transverse_eq (x : ℝ × ℝ × ℝ)
    (hgap :
      DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 1 1 -
        RealSymmetric2.low
          (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
          (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
          (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 1 1) ≠ 0) :
    DFP.SecondLeg.frame x.1 x.2.1 x.2.2 1 0 =
      x.1 ^ 2 * secondFrameTiltFactor x := by
  unfold DFP.SecondLeg.frame
  simp only [EuclideanPlane.frame, Matrix.cons_val_zero,
    RealSymmetric2.lowVector, PiLp.smul_apply, RealSymmetric2.lowRaw,
    Matrix.cons_val_one, smul_eq_mul]
  rw [secondOutputMetric_offDiagonal_eq]
  rw [secondOutputMetric_offDiagonal_eq] at hgap
  unfold secondFrameTiltFactor
  unfold DFP.SecondLeg.frame
  simp only [EuclideanPlane.frame, Matrix.cons_val_zero,
    RealSymmetric2.lowVector, PiLp.smul_apply, RealSymmetric2.lowRaw,
    smul_eq_mul]
  rw [secondOutputMetric_offDiagonal_eq]
  field_simp [hgap]

/-- The denominator of the relative-frame tangent coordinate. -/
private def relativeFrameCosine (x : ℝ × ℝ × ℝ) : ℝ :=
  DFP.FirstLeg.frame x.1 x.2.1 x.2.2 0 0 *
      DFP.SecondLeg.frame x.1 x.2.1 x.2.2 0 0 +
    DFP.FirstLeg.frame x.1 x.2.1 x.2.2 0 1 *
      DFP.SecondLeg.frame x.1 x.2.1 x.2.2 1 0

/-- The relative-frame tangent coordinate after removing its exact factor `ε ^ 2`. -/
private def frameAngleSlopeFactor (x : ℝ × ℝ × ℝ) : ℝ :=
  (firstFrameTiltFactor x * DFP.SecondLeg.frame x.1 x.2.1 x.2.2 0 0 +
      DFP.FirstLeg.frame x.1 x.2.1 x.2.2 1 1 * secondFrameTiltFactor x) /
    relativeFrameCosine x

/-- The weighted relative-frame slope is analytic at the canceled base state. -/
private theorem frameAngleSlopeFactor_analyticAt :
    AnalyticAt ℝ frameAngleSlopeFactor (0, 2, 1) := by
  have hfirstZero := DFP.FirstLeg.frameEntry_analyticAt 0 0
  have hfirstOne := DFP.FirstLeg.frameEntry_analyticAt 0 1
  have hfirstDiag := DFP.FirstLeg.frameEntry_analyticAt 1 1
  have hsecondZero := DFP.SecondLeg.frameEntry_analyticAt 0 0
  have hsecondOne := DFP.SecondLeg.frameEntry_analyticAt 1 0
  have hcosine : AnalyticAt ℝ relativeFrameCosine (0, 2, 1) := by
    unfold relativeFrameCosine
    exact (hfirstZero.mul hsecondZero).add (hfirstOne.mul hsecondOne)
  have hcosineNe : relativeFrameCosine (0, 2, 1) ≠ 0 := by
    norm_num [relativeFrameCosine, DFP.FirstLeg.frame,
      DFP.FirstLeg.outputMetric, DFP.SecondLeg.frame, DFP.SecondLeg.outputMetric,
      DFP.FirstLeg.spectralFactors, DFP.FirstLeg.gradientFactors,
      EuclideanPlane.frame, EuclideanPlane.perp_apply, RealSymmetric2.lowVector,
      RealSymmetric2.lowRaw, RealSymmetric2.low, RealSymmetric2.high,
      RealSymmetric2.gap, RealSymmetric2.lowDenom]
  have hnumerator :=
    (firstFrameTiltFactor_analyticAt.mul hsecondZero).add
      (hfirstDiag.mul secondFrameTiltFactor_analyticAt)
  exact hnumerator.div hcosine hcosineNe

/-- When both low-frame gaps are nonzero, the frame-angle observable is `arctan` of
`ε ^ 2` times the weighted relative-frame slope. -/
private theorem frameAngleIncrement_eq_arctan_weightedSlope
    (x : ℝ × ℝ × ℝ)
    (hfirstGap :
      DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1 -
        RealSymmetric2.low
          (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
          (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
          (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1) ≠ 0)
    (hsecondGap :
      DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 1 1 -
        RealSymmetric2.low
          (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
          (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
          (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 1 1) ≠ 0) :
    (observableMap x).frameAngleIncrement =
      Real.arctan (x.1 ^ 2 * frameAngleSlopeFactor x) := by
  rw [observableMap_frameAngleIncrement]
  unfold EuclideanPlane.SignedAngle.coordinate
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  rw [firstFrame_transverse_eq x hfirstGap,
    secondFrame_transverse_eq x hsecondGap]
  unfold frameAngleSlopeFactor relativeFrameCosine
  rw [secondFrame_transverse_eq x hsecondGap]
  congr 1
  ring

/-- The first low-frame gap whose nonvanishing permits the weighted tilt
reconstruction. -/
private def firstFrameLowGap (x : ℝ × ℝ × ℝ) : ℝ :=
  DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1 -
    RealSymmetric2.low
      (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
      (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
      (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1)

/-- The second low-frame gap whose nonvanishing permits the weighted tilt
reconstruction. -/
private def secondFrameLowGap (x : ℝ × ℝ × ℝ) : ℝ :=
  DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 1 1 -
    RealSymmetric2.low
      (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
      (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
      (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 1 1)

/-- An analytic symmetric metric triple with base value `(0, 0, 1)` has analytic
positive-chart low gap. -/
private theorem metricLowGap_analyticAt
    (a b d : ℝ × ℝ × ℝ → ℝ)
    (ha : AnalyticAt ℝ a (0, 2, 1))
    (hb : AnalyticAt ℝ b (0, 2, 1))
    (hd : AnalyticAt ℝ d (0, 2, 1))
    (hbase : (a (0, 2, 1), b (0, 2, 1), d (0, 2, 1)) =
      ((0, 0, 1) : ℝ × ℝ × ℝ)) :
    AnalyticAt ℝ (fun x ↦ d x - RealSymmetric2.low (a x) (b x) (d x))
      (0, 2, 1) := by
  let entries : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun x ↦ (a x, b x, d x)
  have hentries : AnalyticAt ℝ entries (0, 2, 1) :=
    ha.prod (hb.prod hd)
  have hlowOuter := RealSymmetric2.analyticOnNhd_low
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  have hentriesBase : entries (0, 2, 1) = ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    exact hbase
  rw [← hentriesBase] at hlowOuter
  have hlowComposed := hlowOuter.comp hentries
  have hlow : AnalyticAt ℝ
      (fun x ↦ RealSymmetric2.low (a x) (b x) (d x)) (0, 2, 1) := by
    apply hlowComposed.congr
    filter_upwards [] with x
    rfl
  exact hd.sub hlow

/-- The first low-frame gap is analytic at the canceled base state. -/
private theorem firstFrameLowGap_analyticAt :
    AnalyticAt ℝ firstFrameLowGap (0, 2, 1) := by
  have hzero := DFP.FirstLeg.outputMetricEntry_analyticAt 0 0
  have hone := DFP.FirstLeg.outputMetricEntry_analyticAt 0 1
  have htwo := DFP.FirstLeg.outputMetricEntry_analyticAt 1 1
  have hbase :
      (DFP.FirstLeg.outputMetric 0 2 1 0 0,
        DFP.FirstLeg.outputMetric 0 2 1 0 1,
        DFP.FirstLeg.outputMetric 0 2 1 1 1) =
          ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    norm_num [DFP.FirstLeg.outputMetric]
  have hgap := metricLowGap_analyticAt
    (fun x ↦ DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
    (fun x ↦ DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
    (fun x ↦ DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1)
    hzero hone htwo hbase
  apply hgap.congr
  filter_upwards [] with x
  rfl

/-- The second low-frame gap is analytic at the canceled base state. -/
private theorem secondFrameLowGap_analyticAt :
    AnalyticAt ℝ secondFrameLowGap (0, 2, 1) := by
  have hzero := DFP.SecondLeg.outputMetricEntry_analyticAt 0 0
  have hone := DFP.SecondLeg.outputMetricEntry_analyticAt 0 1
  have htwo := DFP.SecondLeg.outputMetricEntry_analyticAt 1 1
  have hspectralBase : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradientBase : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  have hbase :
      (DFP.SecondLeg.outputMetric 0 2 1 0 0,
        DFP.SecondLeg.outputMetric 0 2 1 0 1,
        DFP.SecondLeg.outputMetric 0 2 1 1 1) =
          ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    norm_num [DFP.SecondLeg.outputMetric, hspectralBase, hgradientBase]
  have hgap := metricLowGap_analyticAt
    (fun x ↦ DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
    (fun x ↦ DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
    (fun x ↦ DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 1 1)
    hzero hone htwo hbase
  apply hgap.congr
  filter_upwards [] with x
  rfl

/-- Fifth-order errors in the two graph coordinates perturb the local real cycle-frame
increment by `O(ε ^ 7)` along the slow-graph jet. -/
theorem frameAngleIncrementStabilityUnderGraphJets (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet :
      (fun ε ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).frameAngleIncrement -
        (observableMap (slowGraphJetPath ε)).frameAngleIncrement) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  let x : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p ε, h ε)
  let x₀ : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p₀ ε, h₀ ε)
  let slope : ℝ → ℝ := fun ε ↦
    ε ^ 2 * frameAngleSlopeFactor (x ε)
  let slope₀ : ℝ → ℝ := fun ε ↦
    ε ^ 2 * frameAngleSlopeFactor (x₀ ε)
  have hpDiff : (fun ε ↦ p ε - p₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀] using h_pJet
  have hhDiff : (fun ε ↦ h ε - h₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀] using h_hJet
  have hpowFiveTendsto : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hp₀Tendsto : Tendsto p₀ (𝓝 0) (𝓝 2) := by
    have hcontinuous : ContinuousAt p₀ 0 := by
      dsimp only [p₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [p₀]
  have hh₀Tendsto : Tendsto h₀ (𝓝 0) (𝓝 1) := by
    have hcontinuous : ContinuousAt h₀ 0 := by
      dsimp only [h₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [h₀]
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpowFiveTendsto).add hp₀Tendsto
  have hhTendsto : Tendsto h (𝓝 0) (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using
      (hhDiff.trans_tendsto hpowFiveTendsto).add hh₀Tendsto
  have hxTendsto : Tendsto x (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [x, id_eq, nhds_prod_eq] using
      tendsto_id.prodMk (hpTendsto.prodMk hhTendsto)
  have hx₀Tendsto : Tendsto x₀ (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [x₀, id_eq, nhds_prod_eq] using
      tendsto_id.prodMk (hp₀Tendsto.prodMk hh₀Tendsto)
  have hslopeFactorDiff :
      (fun ε ↦ frameAngleSlopeFactor (x ε) -
        frameAngleSlopeFactor (x₀ ε)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 5) := by
    have hstability := smoothFrameSlopeStabilityUnderGraphJets
      frameAngleSlopeFactor frameAngleSlopeFactor_analyticAt.contDiffAt
      p h h_pJet h_hJet
    simpa only [x, x₀, p₀, h₀, slowGraphJetPath_apply] using hstability
  have hweightedRaw :=
    (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 2) (𝓝 0)).mul
      hslopeFactorDiff
  have hweighted : (fun ε ↦ slope ε - slope₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
    have hleft (ε : ℝ) :
        ε ^ 2 *
            (frameAngleSlopeFactor (x ε) - frameAngleSlopeFactor (x₀ ε)) =
          slope ε - slope₀ ε := by
      dsimp only [slope, slope₀]
      ring
    have hright (ε : ℝ) : ε ^ 2 * ε ^ 5 = ε ^ 7 := by
      ring
    exact hweightedRaw.congr'
      (Eventually.of_forall hleft) (Eventually.of_forall hright)
  have hpowTwoTendsto : Tendsto (fun ε : ℝ ↦ ε ^ 2) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 2) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hslopeFactorTendsto :
      Tendsto (fun ε ↦ frameAngleSlopeFactor (x ε)) (𝓝 0)
        (𝓝 (frameAngleSlopeFactor (0, 2, 1))) :=
    frameAngleSlopeFactor_analyticAt.continuousAt.tendsto.comp hxTendsto
  have hslope₀FactorTendsto :
      Tendsto (fun ε ↦ frameAngleSlopeFactor (x₀ ε)) (𝓝 0)
        (𝓝 (frameAngleSlopeFactor (0, 2, 1))) :=
    frameAngleSlopeFactor_analyticAt.continuousAt.tendsto.comp hx₀Tendsto
  have hslopeTendsto : Tendsto slope (𝓝 0) (𝓝 0) := by
    have hproduct := hpowTwoTendsto.mul hslopeFactorTendsto
    simpa only [slope, zero_mul] using hproduct
  have hslope₀Tendsto : Tendsto slope₀ (𝓝 0) (𝓝 0) := by
    have hproduct := hpowTwoTendsto.mul hslope₀FactorTendsto
    simpa only [slope₀, zero_mul] using hproduct
  have harctanDiff :
      (fun ε ↦ Real.arctan (slope ε) - Real.arctan (slope₀ ε)) =O[𝓝 0]
        (fun ε ↦ slope ε - slope₀ ε) := by
    have harctanSmooth : ContDiffAt ℝ 1 Real.arctan 0 :=
      Real.contDiff_arctan.contDiffAt
    have harctanStrict := harctanSmooth.hasStrictFDerivAt one_ne_zero
    have houter := harctanStrict.isBigO_sub
    have hpairs : Tendsto (fun ε ↦ (slope ε, slope₀ ε)) (𝓝 0)
        (𝓝 ((0, 0) : ℝ × ℝ)) := by
      simpa only [nhds_prod_eq] using hslopeTendsto.prodMk hslope₀Tendsto
    have hcomposed := houter.comp_tendsto hpairs
    simpa only [Function.comp_def] using hcomposed
  have harctanWeighted :
      (fun ε ↦ Real.arctan (slope ε) - Real.arctan (slope₀ ε)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) :=
    harctanDiff.trans hweighted
  have hfirstGapBase : firstFrameLowGap (0, 2, 1) ≠ 0 := by
    norm_num [firstFrameLowGap, DFP.FirstLeg.outputMetric,
      RealSymmetric2.low, RealSymmetric2.gap]
  have hspectralBase : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradientBase : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  have hsecondGapBase : secondFrameLowGap (0, 2, 1) ≠ 0 := by
    norm_num [secondFrameLowGap, DFP.SecondLeg.outputMetric, hspectralBase,
      hgradientBase, RealSymmetric2.low, RealSymmetric2.gap]
  have hfirstGapX : ∀ᶠ ε in 𝓝 (0 : ℝ), firstFrameLowGap (x ε) ≠ 0 :=
    (firstFrameLowGap_analyticAt.continuousAt.tendsto.comp hxTendsto).eventually_ne
      hfirstGapBase
  have hsecondGapX : ∀ᶠ ε in 𝓝 (0 : ℝ), secondFrameLowGap (x ε) ≠ 0 :=
    (secondFrameLowGap_analyticAt.continuousAt.tendsto.comp hxTendsto).eventually_ne
      hsecondGapBase
  have hfirstGapX₀ : ∀ᶠ ε in 𝓝 (0 : ℝ), firstFrameLowGap (x₀ ε) ≠ 0 :=
    (firstFrameLowGap_analyticAt.continuousAt.tendsto.comp hx₀Tendsto).eventually_ne
      hfirstGapBase
  have hsecondGapX₀ : ∀ᶠ ε in 𝓝 (0 : ℝ), secondFrameLowGap (x₀ ε) ≠ 0 :=
    (secondFrameLowGap_analyticAt.continuousAt.tendsto.comp hx₀Tendsto).eventually_ne
      hsecondGapBase
  have hangleX : ∀ᶠ ε in 𝓝 (0 : ℝ),
      (observableMap (x ε)).frameAngleIncrement = Real.arctan (slope ε) := by
    filter_upwards [hfirstGapX, hsecondGapX] with ε hfirst hsecond
    have hfirst' :
        DFP.FirstLeg.outputMetric (x ε).1 (x ε).2.1 (x ε).2.2 1 1 -
          RealSymmetric2.low
            (DFP.FirstLeg.outputMetric (x ε).1 (x ε).2.1 (x ε).2.2 0 0)
            (DFP.FirstLeg.outputMetric (x ε).1 (x ε).2.1 (x ε).2.2 0 1)
            (DFP.FirstLeg.outputMetric (x ε).1 (x ε).2.1 (x ε).2.2 1 1) ≠ 0 := by
      simpa only [firstFrameLowGap] using hfirst
    have hsecond' :
        DFP.SecondLeg.outputMetric (x ε).1 (x ε).2.1 (x ε).2.2 1 1 -
          RealSymmetric2.low
            (DFP.SecondLeg.outputMetric (x ε).1 (x ε).2.1 (x ε).2.2 0 0)
            (DFP.SecondLeg.outputMetric (x ε).1 (x ε).2.1 (x ε).2.2 0 1)
            (DFP.SecondLeg.outputMetric (x ε).1 (x ε).2.1 (x ε).2.2 1 1) ≠ 0 := by
      simpa only [secondFrameLowGap] using hsecond
    simpa only [slope, x] using
      frameAngleIncrement_eq_arctan_weightedSlope (x ε) hfirst' hsecond'
  have hangleX₀ : ∀ᶠ ε in 𝓝 (0 : ℝ),
      (observableMap (x₀ ε)).frameAngleIncrement = Real.arctan (slope₀ ε) := by
    filter_upwards [hfirstGapX₀, hsecondGapX₀] with ε hfirst hsecond
    have hfirst' :
        DFP.FirstLeg.outputMetric (x₀ ε).1 (x₀ ε).2.1 (x₀ ε).2.2 1 1 -
          RealSymmetric2.low
            (DFP.FirstLeg.outputMetric (x₀ ε).1 (x₀ ε).2.1 (x₀ ε).2.2 0 0)
            (DFP.FirstLeg.outputMetric (x₀ ε).1 (x₀ ε).2.1 (x₀ ε).2.2 0 1)
            (DFP.FirstLeg.outputMetric (x₀ ε).1 (x₀ ε).2.1 (x₀ ε).2.2 1 1) ≠ 0 := by
      simpa only [firstFrameLowGap] using hfirst
    have hsecond' :
        DFP.SecondLeg.outputMetric (x₀ ε).1 (x₀ ε).2.1 (x₀ ε).2.2 1 1 -
          RealSymmetric2.low
            (DFP.SecondLeg.outputMetric (x₀ ε).1 (x₀ ε).2.1 (x₀ ε).2.2 0 0)
            (DFP.SecondLeg.outputMetric (x₀ ε).1 (x₀ ε).2.1 (x₀ ε).2.2 0 1)
            (DFP.SecondLeg.outputMetric (x₀ ε).1 (x₀ ε).2.1 (x₀ ε).2.2 1 1) ≠ 0 := by
      simpa only [secondFrameLowGap] using hsecond
    simpa only [slope₀, x₀] using
      frameAngleIncrement_eq_arctan_weightedSlope (x₀ ε) hfirst' hsecond'
  have hangleDifference : ∀ᶠ ε in 𝓝 (0 : ℝ),
      (observableMap (x ε)).frameAngleIncrement -
          (observableMap (x₀ ε)).frameAngleIncrement =
        Real.arctan (slope ε) - Real.arctan (slope₀ ε) := by
    filter_upwards [hangleX, hangleX₀] with ε hx hx₀
    rw [hx, hx₀]
  have hpowerSame (ε : ℝ) : ε ^ 7 = ε ^ 7 := by
    rfl
  have hresult := harctanWeighted.congr'
    (Filter.EventuallyEq.symm hangleDifference) (Eventually.of_forall hpowerSame)
  simpa only [x, x₀, p₀, h₀, slowGraphJetPath_apply] using hresult

/-- Graph-coordinate functions with the prescribed fifth-order slow-graph jets have
local real cycle-frame increment
`-3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6 + O(ε ^ 7)`. -/
theorem frameAngleExpansionOfGraphJets (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet :
      (fun ε ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).frameAngleIncrement -
        (-3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  have h_stability := frameAngleIncrementStabilityUnderGraphJets p h h_pJet h_hJet
  have h_expansion := h_stability.add slowGraphFrameAngleRemainder
  simpa only [sub_eq_add_neg, add_assoc, neg_add_cancel_left] using h_expansion

end

end DFP.TwoLeg
