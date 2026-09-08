module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.PolarGradientAngleLift
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.PolarGradientAngleError.Basic
import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientAngleGap
import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterTailUniform
import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientLimit
import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.Specialization
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

noncomputable section

open Filter
open scoped Asymptotics EuclideanSpace Topology

namespace DFP.TwoPhaseOrbit

/-- The two normalized endpoint-angle observables tend to zero along any path with
the prescribed slow-graph jets. -/
private theorem endpointAngleIncrements_tendsto_zero (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    Tendsto (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap
        (ε, p ε, h ε)).firstEndpointAngleIncrement.toReal) (𝓝 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap
        (ε, p ε, h ε)).secondEndpointAngleIncrement.toReal) (𝓝 0) (𝓝 0) := by
  have hpow : Tendsto (fun ε : ℝ ↦ ε ^ 2) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 2) 0 := by
      fun_prop
    simpa using hcontinuous.tendsto
  have hfirstError :=
    DFP.TwoLeg.EndpointAngleJet.firstLeadingOfGraphJets p h h_pJet h_hJet
  have hfirstErrorTendsto := hfirstError.trans_tendsto hpow
  have hfirstLeading : Tendsto (fun ε : ℝ ↦ -2 * ε ^ 2) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ -2 * ε ^ 2) 0 := by
      fun_prop
    simpa using hcontinuous.tendsto
  have hfirst : Tendsto (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap
        (ε, p ε, h ε)).firstEndpointAngleIncrement.toReal) (𝓝 0) (𝓝 0) := by
    simpa only [sub_add_cancel, zero_add] using
      hfirstErrorTendsto.add hfirstLeading
  have hsecondError :=
    DFP.TwoLeg.EndpointAngleJet.secondLeadingOfGraphJets p h h_pJet h_hJet
  have hsecondErrorTendsto := hsecondError.trans_tendsto hpow
  have hsecondLeading : Tendsto (fun ε : ℝ ↦ -(ε ^ 2)) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ -(ε ^ 2)) 0 := by
      fun_prop
    simpa using hcontinuous.tendsto
  have hsecond : Tendsto (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap
        (ε, p ε, h ε)).secondEndpointAngleIncrement.toReal) (𝓝 0) (𝓝 0) := by
    simpa only [sub_add_cancel, zero_add] using
      hsecondErrorTendsto.add hsecondLeading
  exact ⟨hfirst, hsecond⟩

/-- The initial endpoint-gradient direction tends to the zero angle along any path
with the prescribed slow-graph jets. -/
private theorem initialGradientAngle_tendsto_zero (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    Tendsto (fun ε : ℝ ↦
      (EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (!₂[(1 : ℝ), p ε * ε ^ 2] : EuclideanSpace ℝ (Fin 2))).toReal)
      (𝓝 0) (𝓝 0) := by
  have hpath := slowGraphPath_tendsto p h h_pJet h_hJet
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    have hprojection : ContinuousAt
        (fun x : ℝ × ℝ × ℝ ↦ x.2.1) (0, 2, 1) := by
      fun_prop
    have ht := hprojection.tendsto.comp hpath
    simpa only [Function.comp_def] using ht
  have hsquare : Tendsto (fun ε : ℝ ↦ ε ^ 2) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 2) 0 := by
      fun_prop
    simpa using hcontinuous.tendsto
  have hproduct : Tendsto (fun ε : ℝ ↦ p ε * ε ^ 2) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using hpTendsto.mul hsquare
  have harctan : Tendsto (fun ε : ℝ ↦ Real.arctan (p ε * ε ^ 2))
      (𝓝 0) (𝓝 0) := by
    have ht := Real.continuousAt_arctan.tendsto.comp hproduct
    simpa only [Function.comp_def, Real.arctan_zero] using ht
  refine harctan.congr' ?_
  filter_upwards [] with ε
  have hone : (0 : ℝ) < 1 := zero_lt_one
  have hformula := EuclideanPlane.oangle_toReal_eq_arctan_sub_of_pos
    1 0 1 (p ε * ε ^ 2) hone hone
  have hbasis : EuclideanSpace.basisFun (Fin 2) ℝ 0 =
      (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) := by
    ext i
    fin_cases i
    · simp [EuclideanSpace.basisFun_apply]
    · simp [EuclideanSpace.basisFun_apply]
  rw [hbasis]
  simpa using hformula.symm

/-- A cubic perturbation of a vector with a uniform lower norm bound has a uniformly
cubic oriented-angle error and remains nonzero. -/
private theorem radialPerturbationAngleBounds
    (g e : EuclideanSpace ℝ (Fin 2)) (ρ K ε : ℝ)
    (hρ : 0 < ρ) (hg : 2 * ρ ≤ ‖g‖)
    (he : ‖e‖ ≤ K * ε ^ 3) (hesmall : K * ε ^ 3 ≤ ρ / 32) :
    ρ ≤ ‖g + e‖ ∧
      |(EuclideanPlane.orientation.oangle g (g + e)).toReal| ≤
        (Real.pi * K / ρ) * ε ^ 3 ∧
      |(EuclideanPlane.orientation.oangle g (g + e)).toReal| < Real.pi / 16 := by
  have hcancel : (g + e) - e = g := by
    abel
  have htriangle : ‖g‖ ≤ ‖g + e‖ + ‖e‖ := by
    calc
      ‖g‖ = ‖(g + e) - e‖ := congrArg norm hcancel.symm
      _ ≤ ‖g + e‖ + ‖e‖ := norm_sub_le _ _
  have hradial : ρ ≤ ‖g + e‖ := by
    linarith
  have hρTwo : ρ ≤ 2 * ρ := by
    linarith
  have hbase : ρ ≤ ‖g‖ := hρTwo.trans hg
  have hperturbIdentity : (g + e) - g = e := by
    abel
  have hperturb : |(EuclideanPlane.orientation.oangle g (g + e)).toReal| ≤
      Real.pi * (K * ε ^ 3) / ρ := by
    apply abs_oangle_toReal_le_of_norm_perturbation
      EuclideanPlane.orientation g (g + e) ρ (K * ε ^ 3) hρ hbase hradial
    rw [hperturbIdentity]
    exact he
  have hquantitative : |(EuclideanPlane.orientation.oangle g (g + e)).toReal| ≤
      (Real.pi * K / ρ) * ε ^ 3 := by
    calc
      _ ≤ Real.pi * (K * ε ^ 3) / ρ := hperturb
      _ = (Real.pi * K / ρ) * ε ^ 3 := by ring
  have hsmall : |(EuclideanPlane.orientation.oangle g (g + e)).toReal| <
      Real.pi / 16 := by
    calc
      _ ≤ Real.pi * (K * ε ^ 3) / ρ := hperturb
      _ ≤ Real.pi * (ρ / 32) / ρ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hesmall Real.pi_pos.le) hρ.le
      _ = Real.pi / 32 := by field_simp [hρ.ne']
      _ < Real.pi / 16 := by nlinarith [Real.pi_pos]
  exact ⟨hradial, hquantitative, hsmall⟩

/-- Small gradient-angle gaps and small radial corrections force every consecutive
endpoint polar-angle gap into a common quarter-turn chart. -/
private theorem endpointPolarAngleGap_small
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2))
    (hgradientNe : ∀ k : ℕ, orbit.endpointGradient k ≠ 0)
    (hradialNe : ∀ k : ℕ, orbit.endpoint k - C ≠ 0)
    (hgradientGap : ∀ k : ℕ,
      |(orbit.endpointGradientAngle (k + 1) - orbit.endpointGradientAngle k).toReal| <
        Real.pi / 16)
    (hcorrection : ∀ k : ℕ,
      |(EuclideanPlane.orientation.oangle (orbit.endpointGradient k)
        (orbit.endpoint k - C)).toReal| < Real.pi / 16) :
    ∀ k : ℕ, |(orbit.endpointPolarAngle C (k + 1) -
      orbit.endpointPolarAngle C k).toReal| < Real.pi / 4 := by
  intro k
  let a := (EuclideanPlane.orientation.oangle (orbit.endpointGradient k)
    (orbit.endpoint k - C)).toReal
  let b := (orbit.endpointGradientAngle (k + 1) - orbit.endpointGradientAngle k).toReal
  let c := (EuclideanPlane.orientation.oangle (orbit.endpointGradient (k + 1))
    (orbit.endpoint (k + 1) - C)).toReal
  have ha : |a| < Real.pi / 16 := hcorrection k
  have hb : |b| < Real.pi / 16 := hgradientGap k
  have hc : |c| < Real.pi / 16 := hcorrection (k + 1)
  have habs : |b + c - a| < Real.pi / 4 := by
    calc
      |b + c - a| ≤ |b| + |c| + |a| := by
        calc
          _ ≤ |b + c| + |a| := abs_sub _ _
          _ ≤ (|b| + |c|) + |a| := add_le_add (abs_add_le _ _) le_rfl
          _ = |b| + |c| + |a| := by ring
      _ < Real.pi / 4 := by linarith [Real.pi_pos]
  have hcoeA : (a : Real.Angle) =
      EuclideanPlane.orientation.oangle (orbit.endpointGradient k)
        (orbit.endpoint k - C) := by
    dsimp only [a]
    exact Real.Angle.coe_toReal _
  have hcoeB : (b : Real.Angle) =
      orbit.endpointGradientAngle (k + 1) - orbit.endpointGradientAngle k := by
    dsimp only [b]
    exact Real.Angle.coe_toReal _
  have hcoeC : (c : Real.Angle) =
      EuclideanPlane.orientation.oangle (orbit.endpointGradient (k + 1))
        (orbit.endpoint (k + 1) - C) := by
    dsimp only [c]
    exact Real.Angle.coe_toReal _
  have hcoe : ((b + c - a : ℝ) : Real.Angle) =
      orbit.endpointPolarAngle C (k + 1) - orbit.endpointPolarAngle C k := by
    change (b : Real.Angle) + (c : Real.Angle) - (a : Real.Angle) = _
    rw [hcoeA, hcoeB, hcoeC]
    have hk := endpointPolarAngle_sub_gradientAngle orbit C k
      (hgradientNe k) (hradialNe k)
    have hkNext := endpointPolarAngle_sub_gradientAngle orbit C (k + 1)
      (hgradientNe (k + 1)) (hradialNe (k + 1))
    rw [← hk, ← hkNext]
    abel
  have habsPi : |b + c - a| < Real.pi := by
    linarith [habs, Real.pi_pos]
  have hprincipal : b + c - a ∈ Set.Ioc (-Real.pi) Real.pi := by
    have hbounds := abs_lt.mp habsPi
    exact ⟨hbounds.1, hbounds.2.le⟩
  have hreal := congrArg Real.Angle.toReal hcoe
  have hprincipalReal : (((b + c - a : ℝ) : Real.Angle).toReal) = b + c - a :=
    Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hprincipal
  rw [hprincipalReal] at hreal
  rw [← hreal]
  exact habs

/-- A small initial gradient angle and radial correction place the zeroth endpoint
polar angle in the quarter-turn chart. -/
private theorem endpointPolarAngle_zero_small
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2))
    (hgradient : orbit.endpointGradient 0 ≠ 0) (hradial : orbit.endpoint 0 - C ≠ 0)
    (hgradientAngle : |(orbit.endpointGradientAngle 0).toReal| < Real.pi / 16)
    (hcorrection : |(EuclideanPlane.orientation.oangle
      (orbit.endpointGradient 0) (orbit.endpoint 0 - C)).toReal| < Real.pi / 16) :
    |(orbit.endpointPolarAngle C 0).toReal| < Real.pi / 4 := by
  let a := (orbit.endpointGradientAngle 0).toReal
  let b := (EuclideanPlane.orientation.oangle
    (orbit.endpointGradient 0) (orbit.endpoint 0 - C)).toReal
  have ha : |a| < Real.pi / 16 := hgradientAngle
  have hb : |b| < Real.pi / 16 := hcorrection
  have habs : |a + b| < Real.pi / 4 := by
    calc
      |a + b| ≤ |a| + |b| := abs_add_le _ _
      _ < Real.pi / 4 := by linarith [Real.pi_pos]
  have hcoeA : (a : Real.Angle) = orbit.endpointGradientAngle 0 := by
    dsimp only [a]
    exact Real.Angle.coe_toReal _
  have hcoeB : (b : Real.Angle) = EuclideanPlane.orientation.oangle
      (orbit.endpointGradient 0) (orbit.endpoint 0 - C) := by
    dsimp only [b]
    exact Real.Angle.coe_toReal _
  have hcoe : ((a + b : ℝ) : Real.Angle) = orbit.endpointPolarAngle C 0 := by
    change (a : Real.Angle) + (b : Real.Angle) = _
    rw [hcoeA, hcoeB]
    have hquotient := endpointPolarAngle_sub_gradientAngle orbit C 0
      hgradient hradial
    rw [← hquotient]
    abel
  have habsPi : |a + b| < Real.pi := by
    linarith [habs, Real.pi_pos]
  have hprincipal : a + b ∈ Set.Ioc (-Real.pi) Real.pi := by
    have hbounds := abs_lt.mp habsPi
    exact ⟨hbounds.1, hbounds.2.le⟩
  have hreal := congrArg Real.Angle.toReal hcoe
  have hprincipalReal : (((a + b : ℝ) : Real.Angle).toReal) = a + b :=
    Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hprincipal
  rw [hprincipalReal] at hreal
  rw [← hreal]
  exact habs

set_option maxHeartbeats 1000000 in
/-- A common constant controls both endpoint phases of the lifted polar-to-gradient
angle error, while retaining the orbit-scale interval needed by asymptotic corollaries. -/
private theorem slowCurvePolarGradientAngleErrorCubeBound (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kangle > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        (∀ j : ℕ, (orbit.state j).ε ∈ Set.Ioc 0 ε₀) ∧
          ∀ Clim : EuclideanSpace ℝ (Fin 2),
            Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
              ∀ (j : ℕ) (σ : Fin 2),
                |orbit.endpointPolarAngleLift Clim (2 * j + σ.val) -
                    orbit.endpointGradientAngleLift (2 * j + σ.val)| ≤
                  Kangle * (orbit.state j).ε ^ 3 := by
  obtain ⟨ηCenter, hηCenter, Kcenter, hKcenter, hCenter⟩ :=
    slowCurveCenterTailUniformBound p h h_invariant h_pJet h_hJet
  obtain ⟨ηGradient, hηGradient, gmin, hgmin, gmax, hgminmax, hGradient⟩ :=
    slowCurveEndpointGradientNormUniformBounds p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηValid, hηValid, hValid⟩ :=
    ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet ηGraph hηGraph
  obtain ⟨hfirstTendsto, hsecondTendsto⟩ :=
    endpointAngleIncrements_tendsto_zero p h h_pJet h_hJet
  have hinitialTendsto := initialGradientAngle_tendsto_zero p h h_pJet h_hJet
  have hpiSixteenthPos : 0 < Real.pi / 16 := by
    positivity
  have hangleBall : Metric.ball (0 : ℝ) (Real.pi / 16) ∈ 𝓝 0 :=
    Metric.ball_mem_nhds 0 hpiSixteenthPos
  have hangleEventually : ∀ᶠ ε in 𝓝 (0 : ℝ),
      |(EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (!₂[(1 : ℝ), p ε * ε ^ 2] : EuclideanSpace ℝ (Fin 2))).toReal| < Real.pi / 16 ∧
      |(DFP.TwoLeg.observableMap
        (ε, p ε, h ε)).firstEndpointAngleIncrement.toReal| < Real.pi / 16 ∧
      |(DFP.TwoLeg.observableMap
        (ε, p ε, h ε)).secondEndpointAngleIncrement.toReal| < Real.pi / 16 := by
    filter_upwards
      [hinitialTendsto.eventually hangleBall,
       hfirstTendsto.eventually hangleBall,
       hsecondTendsto.eventually hangleBall]
      with ε hinitial hfirst hsecond
    rw [Real.dist_eq, sub_zero] at hinitial hfirst hsecond
    exact ⟨hinitial, hfirst, hsecond⟩
  obtain ⟨r, hr, hrule⟩ := Metric.eventually_nhds_iff.mp hangleEventually
  let ρ : ℝ := gmin / 2
  have hρ : 0 < ρ := half_pos hgmin
  let ηTail : ℝ := ρ / (32 * Kcenter)
  have hthirtyTwo : (0 : ℝ) < 32 := by
    norm_num
  have hηTail : 0 < ηTail :=
    div_pos hρ (mul_pos hthirtyTwo hKcenter)
  let εbar := min ηCenter
    (min ηGradient (min ηGraph (min ηValid (min (r / 2) ηTail))))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηCenter.1 (lt_min hηGradient.1
      (lt_min hηGraph.1 (lt_min hηValid.1 (lt_min (half_pos hr) hηTail))))
  have hεbarLt : εbar < 1 / 4 :=
    (min_le_left _ _).trans_lt hηCenter.2
  have hεbarCenter : εbar ≤ ηCenter := min_le_left _ _
  have hεbarGradient : εbar ≤ ηGradient :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hεbarGraph : εbar ≤ ηGraph :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεbarValid : εbar ≤ ηValid :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hεbarRadius : εbar ≤ r / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hεbarTail : εbar ≤ ηTail :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  let Kangle : ℝ := Real.pi * Kcenter / ρ
  have hKangle : 0 < Kangle :=
    div_pos (mul_pos Real.pi_pos hKcenter) hρ
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, Kangle, hKangle, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεCenter : ε₀ ∈ Set.Ioc 0 ηCenter :=
    ⟨hε₀.1, hε₀.2.trans hεbarCenter⟩
  have hεGradient : ε₀ ∈ Set.Ioc 0 ηGradient :=
    ⟨hε₀.1, hε₀.2.trans hεbarGradient⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans hεbarGraph⟩
  have hεValid : ε₀ ∈ Set.Ioc 0 ηValid :=
    ⟨hε₀.1, hε₀.2.trans hεbarValid⟩
  have hεRadius : ε₀ ≤ r / 2 := hε₀.2.trans hεbarRadius
  have hεTail : ε₀ ≤ ηTail := hε₀.2.trans hεbarTail
  have hvalid (j : ℕ) : State.PhaseValidity (orbit.state j) := by
    simpa only [orbit] using hValid ε₀ hεValid j
  have hεcoord (j : ℕ) : (orbit.state j).ε =
      (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hcoordinates := ofSlowCurve_coordinates p h ε₀ j
    have hcoordinates' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hcoordinates
    simpa only [State.coordinates_def] using congrArg Prod.fst hcoordinates'
  have hgraphCoordinates (j : ℕ) : (orbit.state j).coordinates =
      ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
    obtain ⟨hcoordinateGraph, _⟩ := hGraph ε₀ hεGraph j
    calc
      (orbit.state j).coordinates =
          DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
            simpa only [orbit] using ofSlowCurve_coordinates p h ε₀ j
      _ = ((DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          p (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          h (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) := hcoordinateGraph
      _ = ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
        rw [hεcoord j]
  have hscale (j : ℕ) : (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
    obtain ⟨_, hscaleBounds⟩ := hGraph ε₀ hεGraph j
    rw [hεcoord j]
    exact hscaleBounds
  refine ⟨hscale, ?_⟩
  intro Clim hClim
  have hgradientBounds (k : ℕ) :
      ‖orbit.endpointGradient k‖ ∈ Set.Icc gmin gmax := by
    simpa only [orbit] using hGradient ε₀ hεGradient k
  have hgradientNe (k : ℕ) : orbit.endpointGradient k ≠ 0 := by
    exact norm_pos_iff.mp (hgmin.trans_le (hgradientBounds k).1)
  have htail (j : ℕ) : ‖(orbit.state j).center - Clim‖ +
      ‖(orbit.state j).middleCenter - Clim‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 := by
    simpa only [orbit] using hCenter ε₀ hεCenter Clim hClim j
  have hcenterEven (j : ℕ) : ‖(orbit.state j).center - Clim‖ ≤
      Kcenter * (orbit.state j).ε ^ 3 :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (htail j)
  have hcenterOdd (j : ℕ) : ‖(orbit.state j).middleCenter - Clim‖ ≤
      Kcenter * (orbit.state j).ε ^ 3 :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans (htail j)
  have hquarterLeOne : (1 / 4 : ℝ) ≤ 1 := by
    norm_num
  have htailSmall (j : ℕ) : Kcenter * (orbit.state j).ε ^ 3 ≤ ρ / 32 := by
    have hεone : (orbit.state j).ε ≤ 1 :=
      (hscale j).2.trans (hε₀.2.trans (hεbarLt.le.trans hquarterLeOne))
    have hpower : (orbit.state j).ε ^ 3 ≤ (orbit.state j).ε := by
      nlinarith [sq_nonneg ((orbit.state j).ε), (hscale j).1]
    calc
      Kcenter * (orbit.state j).ε ^ 3 ≤ Kcenter * (orbit.state j).ε :=
        mul_le_mul_of_nonneg_left hpower hKcenter.le
      _ ≤ Kcenter * ηTail :=
        mul_le_mul_of_nonneg_left ((hscale j).2.trans hεTail) hKcenter.le
      _ = ρ / 32 := by
        dsimp only [ηTail]
        field_simp [hKcenter.ne']
  have hpointEven (j : ℕ) : orbit.endpoint (2 * j) - Clim =
      orbit.endpointGradient (2 * j) + ((orbit.state j).center - Clim) := by
    rw [endpoint_even, endpointGradient_even, State.center_def]
    abel
  have hpointOdd (j : ℕ) : orbit.endpoint (2 * j + 1) - Clim =
      orbit.endpointGradient (2 * j + 1) +
        ((orbit.state j).middleCenter - Clim) := by
    rw [endpoint_odd, endpointGradient_odd, State.middleCenter_def]
    abel
  have hperturbEven (j : ℕ) :
      ρ ≤ ‖orbit.endpoint (2 * j) - Clim‖ ∧
      |(EuclideanPlane.orientation.oangle (orbit.endpointGradient (2 * j))
        (orbit.endpoint (2 * j) - Clim)).toReal| ≤
          Kangle * (orbit.state j).ε ^ 3 ∧
      |(EuclideanPlane.orientation.oangle (orbit.endpointGradient (2 * j))
        (orbit.endpoint (2 * j) - Clim)).toReal| < Real.pi / 16 := by
    rw [hpointEven]
    have hgradientLower : 2 * ρ ≤ ‖orbit.endpointGradient (2 * j)‖ := by
      dsimp only [ρ]
      nlinarith [(hgradientBounds (2 * j)).1]
    simpa only [Kangle] using radialPerturbationAngleBounds
      (orbit.endpointGradient (2 * j)) ((orbit.state j).center - Clim)
      ρ Kcenter (orbit.state j).ε hρ hgradientLower
      (hcenterEven j) (htailSmall j)
  have hperturbOdd (j : ℕ) :
      ρ ≤ ‖orbit.endpoint (2 * j + 1) - Clim‖ ∧
      |(EuclideanPlane.orientation.oangle (orbit.endpointGradient (2 * j + 1))
        (orbit.endpoint (2 * j + 1) - Clim)).toReal| ≤
          Kangle * (orbit.state j).ε ^ 3 ∧
      |(EuclideanPlane.orientation.oangle (orbit.endpointGradient (2 * j + 1))
        (orbit.endpoint (2 * j + 1) - Clim)).toReal| < Real.pi / 16 := by
    rw [hpointOdd]
    have hgradientLower : 2 * ρ ≤ ‖orbit.endpointGradient (2 * j + 1)‖ := by
      dsimp only [ρ]
      nlinarith [(hgradientBounds (2 * j + 1)).1]
    simpa only [Kangle] using radialPerturbationAngleBounds
      (orbit.endpointGradient (2 * j + 1)) ((orbit.state j).middleCenter - Clim)
      ρ Kcenter (orbit.state j).ε hρ hgradientLower
      (hcenterOdd j) (htailSmall j)
  have hradialNe (k : ℕ) : orbit.endpoint k - Clim ≠ 0 := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · exact norm_pos_iff.mp (hρ.trans_le (hperturbEven j).1)
    · exact norm_pos_iff.mp (hρ.trans_le (hperturbOdd j).1)
  have hcorrectionSmall (k : ℕ) :
      |(EuclideanPlane.orientation.oangle (orbit.endpointGradient k)
        (orbit.endpoint k - Clim)).toReal| < Real.pi / 16 := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · exact (hperturbEven j).2.2
    · exact (hperturbOdd j).2.2
  have hangleLocal (j : ℕ) :
      |(EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (!₂[(1 : ℝ), p (orbit.state j).ε * (orbit.state j).ε ^ 2] :
          EuclideanSpace ℝ (Fin 2))).toReal| < Real.pi / 16 ∧
      |(DFP.TwoLeg.observableMap ((orbit.state j).ε,
        p (orbit.state j).ε, h (orbit.state j).ε)).firstEndpointAngleIncrement.toReal| <
          Real.pi / 16 ∧
      |(DFP.TwoLeg.observableMap ((orbit.state j).ε,
        p (orbit.state j).ε, h (orbit.state j).ε)).secondEndpointAngleIncrement.toReal| <
          Real.pi / 16 := by
    have hdistance : dist (orbit.state j).ε 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (hscale j).1]
      exact ((hscale j).2.trans hεRadius).trans_lt (half_lt_self hr)
    exact hrule hdistance
  have hgradientGapSmall (k : ℕ) :
      |(orbit.endpointGradientAngle (k + 1) - orbit.endpointGradientAngle k).toReal| <
        Real.pi / 16 := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have hgap := endpointGradientAngle_odd_sub_even orbit j (hvalid j)
        (hgradientNe (2 * j)) (hgradientNe (2 * j + 1))
      have hgapReal := congrArg Real.Angle.toReal hgap
      rw [hgapReal]
      simpa only [hgraphCoordinates j] using (hangleLocal j).2.1
    · have hgap := endpointGradientAngle_nextEven_sub_odd orbit j (hvalid j)
        (hgradientNe (2 * j + 1)) (hgradientNe (2 * j + 2))
      have hgapReal := congrArg Real.Angle.toReal hgap
      rw [hgapReal]
      simpa only [hgraphCoordinates j] using (hangleLocal j).2.2
  have hinitialGradientSmall : |(orbit.endpointGradientAngle 0).toReal| <
      Real.pi / 16 := by
    have hzero : orbit.state 0 = State.initial p h ε₀ := by
      simpa only [orbit] using ofSlowCurve_zero p h ε₀
    have hgradientZero : orbit.endpointGradient 0 = (orbit.state 0).gradient := by
      simpa using endpointGradient_even orbit 0
    have hangleZero : orbit.endpointGradientAngle 0 =
        EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
          (!₂[(1 : ℝ), p ε₀ * ε₀ ^ 2] : EuclideanSpace ℝ (Fin 2)) := by
      rw [endpointGradientAngle_def, hgradientZero, hzero, State.gradient_def]
      rw [State.initial_amplitude, State.initial_frame, State.initial_p,
        State.initial_epsilon]
      simp
    rw [hangleZero]
    have hdistance : dist ε₀ 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hε₀.1]
      exact hεRadius.trans_lt (half_lt_self hr)
    exact (hrule hdistance).1
  have hpolarZero : |(orbit.endpointPolarAngle Clim 0).toReal| < Real.pi / 4 :=
    endpointPolarAngle_zero_small orbit Clim
      (hgradientNe 0) (hradialNe 0) hinitialGradientSmall (hcorrectionSmall 0)
  have hsixteenthLeQuarter : Real.pi / 16 ≤ Real.pi / 4 := by
    linarith [Real.pi_pos]
  have hbase := polarGradientLiftDifference_zero_of_small orbit Clim
    (hgradientNe 0) (hradialNe 0) hpolarZero
    (hinitialGradientSmall.trans_le hsixteenthLeQuarter)
  have hpolarGap := endpointPolarAngleGap_small orbit Clim
    hgradientNe hradialNe hgradientGapSmall hcorrectionSmall
  have hdirect := polarGradientLiftDifference_eq_correction_of_small
    orbit Clim hgradientNe hradialNe hbase hpolarGap
    (fun k ↦ (hgradientGapSmall k).trans_le hsixteenthLeQuarter)
    (fun k ↦ (hcorrectionSmall k).trans_le hsixteenthLeQuarter)
  intro j σ
  fin_cases σ
  · change |orbit.endpointPolarAngleLift Clim (2 * j) -
        orbit.endpointGradientAngleLift (2 * j)| ≤
      Kangle * (orbit.state j).ε ^ 3
    rw [hdirect (2 * j)]
    exact (hperturbEven j).2.1
  · change |orbit.endpointPolarAngleLift Clim (2 * j + 1) -
        orbit.endpointGradientAngleLift (2 * j + 1)| ≤
      Kangle * (orbit.state j).ε ^ 3
    rw [hdirect (2 * j + 1)]
    exact (hperturbOdd j).2.1

/-- A uniform cubic bound controls the lifted polar-to-gradient angle error on a
small invariant slow-curve orbit. -/
theorem slowCurvePolarGradientAngleErrorUniform (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kangle > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ (j : ℕ) (σ : Fin 2),
              |orbit.endpointPolarAngleLift Clim (2 * j + σ.val) -
                  orbit.endpointGradientAngleLift (2 * j + σ.val)| ≤
                Kangle * (orbit.state j).ε ^ 3 := by
  obtain ⟨εbar, hεbar, Kangle, hKangle, hcore⟩ :=
    slowCurvePolarGradientAngleErrorCubeBound p h h_invariant h_pJet h_hJet
  refine ⟨εbar, hεbar, Kangle, hKangle, ?_⟩
  intro ε₀ hε₀
  exact (hcore ε₀ hε₀).2
/-- The lifted polar-to-gradient angle error is big-O of the cubic orbit scale
along every endpoint phase of a small invariant slow-curve orbit. -/
theorem slowCurvePolarGradientAngleErrorIsBigO (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ σ : Fin 2,
              (fun j : ℕ ↦ orbit.endpointPolarAngleLift Clim (2 * j + σ.val) -
                orbit.endpointGradientAngleLift (2 * j + σ.val)) =O[atTop]
              (fun j : ℕ ↦ (orbit.state j).ε ^ 3) := by
  obtain ⟨εbarCore, hεbarCore, Kangle, hKangle, hcore⟩ :=
    slowCurvePolarGradientAngleErrorUniform p h h_invariant h_pJet h_hJet
  obtain ⟨εbarGraph, hεbarGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min εbarCore εbarGraph
  have hεbar : εbar ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor
    · exact lt_min hεbarCore.1 hεbarGraph.1
    · exact (min_le_left _ _).trans_lt hεbarCore.2
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  intro Clim hClim σ
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨Kangle, Eventually.of_forall ?_⟩
  intro j
  have hεCore : ε₀ ∈ Set.Ioc 0 εbarCore :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 εbarGraph :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  have hj := hcore ε₀ hεCore Clim hClim j σ
  have hs := (hGraph ε₀ hεGraph j).2.1
  have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
  have hstate : (orbit.state j).ε =
      (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hcoord
  have hj' :
      |orbit.endpointPolarAngleLift Clim (2 * j + σ.val) -
          orbit.endpointGradientAngleLift (2 * j + σ.val)| ≤
        Kangle * (orbit.state j).ε ^ 3 := by
    simpa only [orbit] using hj
  change |(orbit.endpointPolarAngleLift Clim (2 * j + σ.val) -
      orbit.endpointGradientAngleLift (2 * j + σ.val))| ≤
    Kangle * ‖(orbit.state j).ε ^ 3‖
  rw [hstate] at hj'
  rw [hstate, norm_pow, Real.norm_eq_abs, abs_of_pos hs]
  exact hj'

/-- The lifted polar-to-gradient angle error is little-O of the quadratic orbit
scale along every endpoint phase of a small invariant slow-curve orbit. -/
theorem slowCurvePolarGradientAngleErrorIsLittleO (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ σ : Fin 2,
              (fun j : ℕ ↦ orbit.endpointPolarAngleLift Clim (2 * j + σ.val) -
                orbit.endpointGradientAngleLift (2 * j + σ.val)) =o[atTop]
              (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
  obtain ⟨ηCore, hηCore, hbigCore⟩ :=
    slowCurvePolarGradientAngleErrorIsBigO p h h_invariant h_pJet h_hJet
  obtain ⟨ηSum, hηSum, hsum⟩ :=
    DFP.TwoLeg.slowCurveScaleFourthPowerSummable p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min ηCore (min ηSum ηGraph)
  have hεbar : εbar ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor
    · exact lt_min hηCore.1 (lt_min hηSum hηGraph.1)
    · exact (min_le_left _ _).trans_lt hηCore.2
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεCore : ε₀ ∈ Set.Ioc 0 ηCore :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεSum : ε₀ ∈ Set.Ioc 0 ηSum :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hscale : ∀ j : ℕ, (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
    have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀
    intro j
    have hx := hGraph ε₀ hεGraph j
    have hc := hcoord j
    have heq : (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
      simpa only [orbit, DFP.TwoPhaseOrbit.State.coordinates_def] using
        congrArg Prod.fst hc
    rw [heq]
    exact hx.2
  have hεcoord (j : ℕ) : (orbit.state j).ε =
      (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hc := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hc' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hc
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using congrArg Prod.fst hc'
  have hsummable : Summable (fun j : ℕ ↦ (orbit.state j).ε ^ 4) := by
    simpa only [hεcoord] using hsum ε₀ hεSum
  have hfourZero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε ^ 4) atTop (𝓝 0) :=
    hsummable.tendsto_atTop_zero
  have hscaleZero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) := by
    have hquarterPos : (0 : ℝ) < 1 / 4 := by
      norm_num
    have hroot := hfourZero.rpow_const_nhds_zero hquarterPos
    refine hroot.congr' (Eventually.of_forall ?_)
    intro j
    have hfourNe : (4 : ℕ) ≠ 0 := by
      norm_num
    have hid := Real.pow_rpow_inv_natCast (hscale j).1.le hfourNe
    convert hid using 1
    norm_num
  have hcubeLittleSquare : (fun j : ℕ ↦ (orbit.state j).ε ^ 3) =o[atTop]
      (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
    have hsmall : (fun j : ℕ ↦ (orbit.state j).ε) =o[atTop]
        (fun _ : ℕ ↦ (1 : ℝ)) :=
      (Asymptotics.isLittleO_one_iff ℝ).2 hscaleZero
    have hmul := hsmall.mul_isBigO
      (Asymptotics.isBigO_refl (fun j : ℕ ↦ (orbit.state j).ε ^ 2) atTop)
    refine hmul.congr' (Eventually.of_forall ?_) (Eventually.of_forall ?_)
    · intro j
      ring
    · intro j
      simp
  intro Clim hClim σ
  have hbig := hbigCore ε₀ hεCore Clim hClim σ
  exact hbig.trans_isLittleO hcubeLittleSquare

end DFP.TwoPhaseOrbit
