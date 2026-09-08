module

public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondGradientGermTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.Converse
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondGradientGermTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.Converse

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-- Infrastructure I.16a: the independent-radius second-gradient low coordinate has a flat
signed-scale quadratic germ after the source substitution `r = ε ^ 2`. -/
theorem independentRadiusSecondGradientLow_scale_quadraticGerm (p h : ℝ) :
    HasQuadraticGerm
      (fun ε : ℝ ↦
        (independentRadiusSecondGradient ((ε, p, h), ε ^ 2)).1)
      1 0 0 := by
  let F : ((ℝ × ℝ × ℝ) × ℝ) → ℝ :=
    fun z ↦ (independentRadiusSecondGradient z).1
  let θ : ℝ × ℝ × ℝ := (0, p, h)
  let path : ℝ → ((ℝ × ℝ × ℝ) × ℝ) :=
    fun ε ↦ ((ε, p, h), ε ^ 2)
  let basePath : ℝ → ((ℝ × ℝ × ℝ) × ℝ) :=
    fun t ↦ ((t, p, h), 0)
  let radiusPath : ℝ → ((ℝ × ℝ × ℝ) × ℝ) :=
    fun r ↦ (θ, r)
  let dScale : ((ℝ × ℝ × ℝ) × ℝ) := (((1 : ℝ), 0, 0), 0)
  let dRadius : ((ℝ × ℝ × ℝ) × ℝ) := (((0 : ℝ), 0, 0), 1)
  have hθvalue : θ = ((0 : ℝ), p, h) := by
    rfl
  have htwo_le_three : (2 : WithTop ENat) ≤ (3 : WithTop ENat) := by
    norm_num
  have hthree_ne_zero : (3 : WithTop ENat) ≠ 0 := by
    norm_num
  have hFanalytic : AnalyticAt ℝ F (θ, 0) := by
    have hlow := analyticAt_fst.comp (independentRadiusSecondGradient_analyticAt θ)
    have hF_eq : F =
        (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
          (independentRadiusSecondGradient z).1) := by
      rfl
    rw [hF_eq]
    simpa only [Function.comp_def, θ] using hlow
  have hFregular : ContDiffAt ℝ 3 F (θ, 0) := by
    exact hFanalytic.contDiffAt
  have hpathRegular : ContDiffAt ℝ 3 path 0 := by
    dsimp [path]
    fun_prop
  have hbaseRegular : ContDiffAt ℝ 3 basePath 0 := by
    dsimp [basePath]
    fun_prop
  have hradiusRegular : ContDiffAt ℝ 3 radiusPath 0 := by
    dsimp [radiusPath]
    fun_prop
  have hpathDeriv : HasDerivAt path dScale 0 := by
    have hinner : HasDerivAt (fun ε : ℝ ↦ (ε, p, h))
        ((1 : ℝ), (0 : ℝ), (0 : ℝ)) 0 := by
      simpa only [id_eq] using
        (hasDerivAt_id (0 : ℝ)).prodMk
          ((hasDerivAt_const (0 : ℝ) p).prodMk
            (hasDerivAt_const (0 : ℝ) h))
    have hsquare : HasDerivAt (fun ε : ℝ ↦ ε ^ 2) (0 : ℝ) 0 := by
      have hpow := (hasDerivAt_id (0 : ℝ)).pow 2
      have hfun : (id : ℝ → ℝ) ^ 2 = (fun ε : ℝ ↦ ε ^ 2) := by
        funext ε
        rfl
      rw [hfun] at hpow
      apply hpow.congr_deriv
      norm_num
    have h := hinner.prodMk hsquare
    simpa only [path, dScale] using h
  have hbaseDeriv : HasDerivAt basePath dScale 0 := by
    have hinner : HasDerivAt (fun t : ℝ ↦ (t, p, h))
        ((1 : ℝ), (0 : ℝ), (0 : ℝ)) 0 := by
      simpa only [id_eq] using
        (hasDerivAt_id (0 : ℝ)).prodMk
          ((hasDerivAt_const (0 : ℝ) p).prodMk
            (hasDerivAt_const (0 : ℝ) h))
    have hzero : HasDerivAt (fun _ : ℝ ↦ (0 : ℝ)) (0 : ℝ) 0 :=
      hasDerivAt_const (0 : ℝ) 0
    have h := hinner.prodMk hzero
    simpa only [basePath, dScale] using h
  have hradiusDeriv : HasDerivAt radiusPath dRadius 0 := by
    have hinner : HasDerivAt (fun _ : ℝ ↦ θ)
        ((0 : ℝ), (0 : ℝ), (0 : ℝ)) 0 := by
      exact hasDerivAt_const (0 : ℝ) θ
    have hidentity : HasDerivAt (fun r : ℝ ↦ r) (1 : ℝ) 0 :=
      hasDerivAt_id (0 : ℝ)
    have h := hinner.prodMk hidentity
    simpa only [radiusPath, dRadius] using h
  have hpathSecond : iteratedDeriv 2 path 0 =
      (((0 : ℝ), (0 : ℝ), (0 : ℝ)), 2) := by
    have hderivPath : deriv path =
        fun t : ℝ ↦ (((1 : ℝ), (0 : ℝ), (0 : ℝ)), 2 * t) := by
      funext t
      have hinner : HasDerivAt (fun s : ℝ ↦ (s, p, h))
          ((1 : ℝ), (0 : ℝ), (0 : ℝ)) t := by
        simpa only [id_eq] using
          (hasDerivAt_id t).prodMk
            ((hasDerivAt_const t p).prodMk (hasDerivAt_const t h))
      have hsquare : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * t) t := by
        have hpow := (hasDerivAt_id t).pow 2
        have hfun : (id : ℝ → ℝ) ^ 2 = (fun s : ℝ ↦ s ^ 2) := by
          funext s
          rfl
        rw [hfun] at hpow
        apply hpow.congr_deriv
        norm_num
      exact (hinner.prodMk hsquare).deriv
    have hsecond : HasDerivAt
        (fun t : ℝ ↦ (((1 : ℝ), (0 : ℝ), (0 : ℝ)), 2 * t))
        (((0 : ℝ), (0 : ℝ), (0 : ℝ)), 2) 0 := by
      have hconstant : HasDerivAt
          (fun _ : ℝ ↦ ((1 : ℝ), (0 : ℝ), (0 : ℝ)))
          ((0 : ℝ), (0 : ℝ), (0 : ℝ)) 0 := by
        have hconstantRaw := hasDerivAt_const (0 : ℝ)
          ((1 : ℝ), (0 : ℝ), (0 : ℝ))
        apply hconstantRaw.congr_deriv
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · rfl
      have hlinear : HasDerivAt (fun t : ℝ ↦ 2 * t) (2 : ℝ) 0 := by
        have hlinearRaw := (hasDerivAt_const (0 : ℝ) (2 : ℝ)).mul
          (hasDerivAt_id (0 : ℝ))
        apply hlinearRaw.congr_deriv
        norm_num
      exact hconstant.prodMk hlinear
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
    rw [hderivPath]
    exact hsecond.deriv
  have hbaseSecond : iteratedDeriv 2 basePath 0 = 0 := by
    have hderivBase : deriv basePath = fun _ : ℝ ↦ dScale := by
      funext t
      have hinner : HasDerivAt (fun s : ℝ ↦ (s, p, h))
          ((1 : ℝ), (0 : ℝ), (0 : ℝ)) t := by
        simpa only [id_eq] using
          (hasDerivAt_id t).prodMk
            ((hasDerivAt_const t p).prodMk (hasDerivAt_const t h))
      have hzero : HasDerivAt (fun _ : ℝ ↦ (0 : ℝ)) (0 : ℝ) t :=
        hasDerivAt_const t 0
      exact (hinner.prodMk hzero).deriv
    have hconstant : HasDerivAt (fun _ : ℝ ↦ dScale)
        (0 : ((ℝ × ℝ × ℝ) × ℝ)) 0 := by
      have hconstantRaw := hasDerivAt_const (0 : ℝ) dScale
      apply hconstantRaw.congr_deriv
      simp
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
    rw [hderivBase]
    exact hconstant.deriv
  have hbaseValue : (fun t : ℝ ↦ F (basePath t)) = fun _ : ℝ ↦ (1 : ℝ) := by
    funext t
    simp only [F, basePath, independentRadiusSecondGradient_zero]
  have hbaseDerivZero : HasDerivAt (fun t : ℝ ↦ F (basePath t)) 0 0 := by
    rw [hbaseValue]
    exact hasDerivAt_const (0 : ℝ) 1
  have hFderivScale : fderiv ℝ F (θ, 0) dScale = 0 := by
    have hbaseAt : basePath 0 = (θ, 0) := by
      simp [basePath, θ]
    have hFregularBase : ContDiffAt ℝ 3 F (basePath 0) := by
      rw [hbaseAt]
      exact hFregular
    have hchain := hFregularBase.differentiableAt hthree_ne_zero |>.hasFDerivAt
      |>.comp_hasDerivAt 0 hbaseDeriv
    have hunique := hchain.unique hbaseDerivZero
    simpa only [Function.comp_def, basePath, θ, dScale] using hunique
  have hFderivRadius : fderiv ℝ F (θ, 0) dRadius = 0 := by
    have hgradient := independentRadiusSecondGradient_hasDerivAt θ
    have hlow : HasDerivAt
        (fun r : ℝ ↦ (independentRadiusSecondGradient (θ, r)).1) 0 0 := by
      exact hasDerivAt_fst_of_prod hgradient
    have hradiusAt : radiusPath 0 = (θ, 0) := by
      simp [radiusPath]
    have hFregularRadius : ContDiffAt ℝ 3 F (radiusPath 0) := by
      rw [hradiusAt]
      exact hFregular
    have hchain := hFregularRadius.differentiableAt hthree_ne_zero |>.hasFDerivAt
      |>.comp_hasDerivAt 0 hradiusDeriv
    have hlow' : HasDerivAt (F ∘ radiusPath) 0 0 := by
      simpa only [Function.comp_def, F, radiusPath] using hlow
    have hunique := hchain.unique hlow'
    simpa only [Function.comp_def, F, radiusPath, θ, dRadius] using hunique
  have hFregularTwo : ContDiffAt ℝ 2 F (θ, 0) := by
    exact hFregular.of_le htwo_le_three
  have hpathRegularTwo : ContDiffAt ℝ 2 path 0 := by
    exact hpathRegular.of_le htwo_le_three
  have hbaseRegularTwo : ContDiffAt ℝ 2 basePath 0 := by
    exact hbaseRegular.of_le htwo_le_three
  have hbaseComposition := iteratedDeriv_vcomp_two
    (g := F) (f := basePath) (x := 0) hFregularTwo hbaseRegularTwo
  have hbaseCompositionFunction : F ∘ basePath = fun _ : ℝ ↦ (1 : ℝ) := by
    funext t
    exact congrFun hbaseValue t
  have hbaseLeft : iteratedDeriv 2 (F ∘ basePath) 0 = 0 := by
    rw [hbaseCompositionFunction]
    rw [iteratedDeriv_const]
    norm_num
  have hHessianScale :
      iteratedFDeriv ℝ 2 F (θ, 0) (fun _ : Fin 2 ↦ dScale) = 0 := by
    have hbaseDerivValue : deriv basePath 0 = dScale := hbaseDeriv.deriv
    rw [hbaseLeft, hbaseDerivValue, hbaseSecond] at hbaseComposition
    have hzeroEq :
        (0 : ℝ) = iteratedFDeriv ℝ 2 F (θ, 0) (fun _ : Fin 2 ↦ dScale) := by
      simpa only [basePath, θ, Function.comp_apply, Pi.zero_apply,
        ContinuousLinearMap.map_zero, map_zero, add_zero] using hbaseComposition
    exact hzeroEq.symm
  have hpathAt : path 0 = (θ, 0) := by
    simp [path, θ]
  have hFregularPathTwo : ContDiffAt ℝ 2 F (path 0) := by
    rw [hpathAt]
    exact hFregularTwo
  have hpathComposition := iteratedDeriv_vcomp_two
    (g := F) (f := path) (x := 0) hFregularPathTwo hpathRegularTwo
  have hpathSecond' : iteratedDeriv 2 path 0 = (2 : ℝ) • dRadius := by
    rw [hpathSecond]
    norm_num [dRadius]
  have hFderivRadiusTwo : fderiv ℝ F (θ, 0) ((2 : ℝ) • dRadius) = 0 := by
    calc
      fderiv ℝ F (θ, 0) ((2 : ℝ) • dRadius) =
          (2 : ℝ) • fderiv ℝ F (θ, 0) dRadius := by rw [map_smul]
      _ = 0 := by rw [hFderivRadius]; simp
  have hpathDerivValue : deriv path 0 = dScale := hpathDeriv.deriv
  rw [hpathDerivValue, hpathSecond'] at hpathComposition
  dsimp [path] at hpathComposition
  have hzeroPow : (0 : ℝ) ^ 2 = 0 := by
    norm_num
  rw [hzeroPow] at hpathComposition
  rw [← hθvalue, hFderivRadiusTwo, hHessianScale] at hpathComposition
  have hsecond :
      iteratedDeriv 2 (fun ε : ℝ ↦ F (path ε)) 0 = 0 := by
    simpa only [Function.comp_def, Pi.zero_apply, zero_add, add_zero] using hpathComposition
  have hfirst : deriv (fun ε : ℝ ↦ F (path ε)) 0 = 0 := by
    have hFregularPath : ContDiffAt ℝ 3 F (path 0) := by
      rw [hpathAt]
      exact hFregular
    have hchain := hFregularPath.differentiableAt hthree_ne_zero |>.hasFDerivAt
      |>.comp_hasDerivAt 0 hpathDeriv
    have hchainDeriv := hchain.deriv
    rw [hpathAt, hFderivScale] at hchainDeriv
    simpa only [Function.comp_def] using hchainDeriv
  have hzero : (fun ε : ℝ ↦ F (path ε)) 0 = 1 := by
    change F (path 0) = 1
    rw [hpathAt]
    simp only [F, independentRadiusSecondGradient_zero]
  have hregularPath : ContDiffAt ℝ 3 (fun ε : ℝ ↦ F (path ε)) 0 := by
    have hFregularAtPath : ContDiffAt ℝ 3 F (path 0) := by
      rw [hpathAt]
      exact hFregular
    have hcomp : ContDiffAt ℝ 3 (F ∘ path) 0 :=
      ContDiffAt.comp (𝕜 := ℝ) (n := 3) (g := F) (f := path)
        0 hFregularAtPath hpathRegular
    simpa only [Function.comp_def] using hcomp
  have hsecond' : iteratedDeriv 2 (fun ε : ℝ ↦ F (path ε)) 0 = 2 * (0 : ℝ) := by
    simpa using hsecond
  have hgerm := HasQuadraticGerm.of_contDiffAt_iteratedDeriv_two
    (a₂ := (0 : ℝ))
    hregularPath hzero hfirst hsecond'
  simpa only [F, path] using hgerm

end DFP.TwoLeg.Mixed
