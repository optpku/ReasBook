module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_19d_Recursive_unwrapped_frame_angle_represents_the_physical_frame_FrameAngle
public import DFPWolfe.Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample.Infrastructure_I_4b_Local_signed_angle_chart_and_angular_perturbation_bounds
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_4_8c0_Quotient_valued_physical_endpoint_polar_angles
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_8c1_Compatible_real_lifts_of_the_physical_endpoint_polar_angles_PolarAngleLift
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointAngleGap
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointPolarAngleLift.FrameAngle
import all ReasLib.Geometry.Euclidean.Plane.Rotation
import Mathlib.Analysis.Real.Pi.Bounds

public section

noncomputable section

open Filter
open scoped Asymptotics EuclideanSpace Matrix Topology

namespace DFP.TwoPhaseOrbit

/-- Helper for Lemma 4.8c1: the initial slow-curve state has the standard basis
as its physical low vector. -/
lemma slowCurveInitialLowVector (p h : ℝ → ℝ) (ε₀ : ℝ) :
    ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state 0).lowVector =
      EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
  -- Evaluate the initial frame column in standard coordinates.
  rw [DFP.TwoPhaseOrbit.ofSlowCurve_zero]
  ext i
  rw [State.lowVector_apply, State.initial_frame]
  fin_cases i <;> simp [EuclideanSpace.basisFun_apply, Matrix.one_apply]

/-- Helper for Lemma 4.8c1: the initial endpoint lift is the physical correction
when the initial low vector is the standard basis. -/
lemma endpointPolarLiftFrameBase
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2))
    (hinitial : (orbit.state 0).lowVector =
      EuclideanSpace.basisFun (Fin 2) ℝ 0) :
    orbit.endpointPolarAngleLift C 0 - orbit.frameAngle 0 =
      (EuclideanPlane.orientation.oangle (orbit.state 0).lowVector
        (orbit.endpoint 0 - C)).toReal := by
  -- At index zero, the recursive lift and frame angle are their principal values.
  rw [endpointPolarAngleLift_zero, frameAngle_zero, sub_zero]
  rw [endpointPolarAngle_def, hinitial]

/-- Helper for Lemma 4.8c1: at one even endpoint, the frame representation
identifies the lifted polar quotient with the physical low-vector angle. -/
lemma endpointPolarLiftFrameQuotientAt
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ)
    (hlow : (orbit.state j).lowVector ≠ 0)
    (hangle : EuclideanPlane.orientation.oangle
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) (orbit.state j).lowVector =
        (orbit.frameAngle j : Real.Angle))
    (hradial : orbit.endpoint (2 * j) - C ≠ 0) :
    ((orbit.endpointPolarAngleLift C (2 * j) - orbit.frameAngle j : ℝ) :
        Real.Angle) =
      EuclideanPlane.orientation.oangle (orbit.state j).lowVector
        (orbit.endpoint (2 * j) - C) := by
  -- Establish the nonzero standard basis required by the oriented-angle subtraction law.
  have hbasis : (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≠ 0 := by
    intro hzero
    have hcoordinate := congrArg
      (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hzero
    simp [EuclideanSpace.basisFun_apply] at hcoordinate
  change (orbit.endpointPolarAngleLift C (2 * j) : Real.Angle) -
    (orbit.frameAngle j : Real.Angle) = _
  -- Rewrite the lift quotient and substitute the frame angle representation.
  rw [endpointPolarAngleLift_coe, endpointPolarAngle_def, ← hangle]
  exact EuclideanPlane.orientation.oangle_sub_left hbasis hlow hradial

/-- Helper for Lemma 4.8c1: the frame representation supplies the initial and
all even-index quotient identities simultaneously. -/
lemma endpointPolarLiftFrameQuotient
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2))
    (hinitial : (orbit.state 0).lowVector =
      EuclideanSpace.basisFun (Fin 2) ℝ 0)
    (hlow : ∀ j : ℕ, (orbit.state j).lowVector ≠ 0)
    (hangle : ∀ j : ℕ, EuclideanPlane.orientation.oangle
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) (orbit.state j).lowVector =
        (orbit.frameAngle j : Real.Angle))
    (hradial : ∀ k : ℕ, orbit.endpoint k - C ≠ 0) :
    (orbit.endpointPolarAngleLift C 0 - orbit.frameAngle 0 =
        (EuclideanPlane.orientation.oangle (orbit.state 0).lowVector
          (orbit.endpoint 0 - C)).toReal) ∧
      (∀ j : ℕ,
        ((orbit.endpointPolarAngleLift C (2 * j) - orbit.frameAngle j : ℝ) :
            Real.Angle) =
          EuclideanPlane.orientation.oangle (orbit.state j).lowVector
            (orbit.endpoint (2 * j) - C)) := by
  -- Package the base identity with the uniform even-index quotient identity.
  refine ⟨endpointPolarLiftFrameBase orbit C hinitial, ?_⟩
  intro j
  exact endpointPolarLiftFrameQuotientAt orbit C j
    (hlow j) (hangle j) (hradial (2 * j))

/-- The oriented angle from the standard basis to its planar rotation is the
rotation parameter itself. -/
lemma standardBasis_oangle_rotation (φ : ℝ) :
    EuclideanPlane.orientation.oangle
        (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (EuclideanPlane.rotation (φ : Real.Angle)
          (EuclideanSpace.basisFun (Fin 2) ℝ 0)) = (φ : Real.Angle) := by
  have hbasis : (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≠ 0 := by
    intro hz
    have hcoordinate := congrArg
      (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hz
    simp [EuclideanSpace.basisFun_apply] at hcoordinate
  simpa only [EuclideanPlane.rotation] using
    EuclideanPlane.orientation.oangle_rotation_self_right hbasis φ

/-- The Lemma 4.8c1 slow-graph gradient angle tends to the principal branch at the
base point, uniformly after restricting the scale to a small metric ball. -/
theorem slowCurveInitialGradientAngle_tendsto_zero (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    Tendsto (fun ε : ℝ ↦
      (EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (!₂[(1 : ℝ), p ε * ε ^ 2] : EuclideanSpace ℝ (Fin 2))).toReal)
      (𝓝 0) (𝓝 0) := by
  -- The graph jets first give convergence of the shape coordinate and its slope.
  have hpath := DFP.TwoPhaseOrbit.slowGraphPath_tendsto p h h_pJet h_hJet
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

/-- The Lemma 4.8c1 low-vector to even-gradient angle is the coordinate slope
angle in the current oriented frame. -/
theorem lowVector_gradientAngle_toReal_eq
    (s : DFP.TwoPhaseOrbit.State)
    (hs : DFP.TwoPhaseOrbit.State.PhaseValidity s) :
    (EuclideanPlane.orientation.oangle s.lowVector s.gradient).toReal =
      (EuclideanPlane.orientation.oangle
        (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2))
        (!₂[(1 : ℝ), s.p * s.ε ^ 2] : EuclideanSpace ℝ (Fin 2))).toReal := by
  -- Replace both physical vectors by their common frame coordinates.
  have hlow : s.lowVector = WithLp.toLp 2 (s.frame *ᵥ ![(1 : ℝ), 0]) := by
    ext i
    rw [DFP.TwoPhaseOrbit.State.lowVector_apply]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hlow, DFP.TwoPhaseOrbit.State.gradient_def]
  rw [EuclideanPlane.orientation.oangle_smul_right_of_pos _ _ hs.amplitude_pos]
  rw [EuclideanPlane.oangle_specialOrthogonal_mulVec s.frame
    hs.frame_specialOrthogonal 1 0 1 (s.p * s.ε ^ 2)]

/-- A small radial perturbation has a uniformly small oriented-angle error when
the unperturbed gradient has a positive norm lower bound. -/
theorem radialPerturbationAngleBounds
    (g e : EuclideanSpace ℝ (Fin 2)) (ρ K ε : ℝ)
    (hρ : 0 < ρ) (hg : 2 * ρ ≤ ‖g‖)
    (he : ‖e‖ ≤ K * ε ^ 3) (hesmall : K * ε ^ 3 ≤ ρ / 32) :
    ρ ≤ ‖g + e‖ ∧
      |(EuclideanPlane.orientation.oangle g (g + e)).toReal| ≤
        (Real.pi * K / ρ) * ε ^ 3 ∧
      |(EuclideanPlane.orientation.oangle g (g + e)).toReal| < Real.pi / 16 := by
  -- The triangle inequality supplies the output norm lower bound needed by the angle chart.
  have hcancel : (g + e) - e = g := by
    abel
  have htriangle : ‖g‖ ≤ ‖g + e‖ + ‖e‖ := by
    calc
      ‖g‖ = ‖(g + e) - e‖ := congrArg norm hcancel.symm
      _ ≤ ‖g + e‖ + ‖e‖ := norm_sub_le _ _
  have hradial : ρ ≤ ‖g + e‖ := by
    linarith
  have hbase : ρ ≤ ‖g‖ := by
    linarith
  have hperturbIdentity : (g + e) - g = e := by
    abel
  have hperturb : |(EuclideanPlane.orientation.oangle g (g + e)).toReal| ≤
      Real.pi * (K * ε ^ 3) / ρ := by
    apply DFP.TwoPhaseOrbit.abs_oangle_toReal_le_of_norm_perturbation
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

/-- The Lemma 4.8c1 sum of two principal oriented-angle representatives remains
principal and is bounded by the sum of their absolute values. -/
theorem oangle_toReal_add_small
    (u v w : EuclideanSpace ℝ (Fin 2))
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (ha : |(EuclideanPlane.orientation.oangle u v).toReal| < Real.pi / 16)
    (hb : |(EuclideanPlane.orientation.oangle v w).toReal| < Real.pi / 16) :
    |(EuclideanPlane.orientation.oangle u w).toReal| < Real.pi / 8 := by
  let a := (EuclideanPlane.orientation.oangle u v).toReal
  let b := (EuclideanPlane.orientation.oangle v w).toReal
  have habs : |a + b| < Real.pi / 8 := by
    calc
      |a + b| ≤ |a| + |b| := abs_add_le _ _
      _ < Real.pi / 8 := by linarith [Real.pi_pos]
  have hcoe : ((a + b : ℝ) : Real.Angle) =
      EuclideanPlane.orientation.oangle u w := by
    change (a : Real.Angle) + (b : Real.Angle) = _
    rw [show (a : Real.Angle) = EuclideanPlane.orientation.oangle u v by
      exact Real.Angle.coe_toReal _,
      show (b : Real.Angle) = EuclideanPlane.orientation.oangle v w by
        exact Real.Angle.coe_toReal _]
    exact EuclideanPlane.orientation.oangle_add hu hv hw
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

end DFP.TwoPhaseOrbit

/-- Lemma 4.8c1 (Compatible real lifts of the physical endpoint polar angles):
below one common slow-curve threshold, consecutive lifted endpoint angles are
the unique small signed representatives of their quotient-valued gaps, and the
even lifts differ from the physical frame lift by the endpoint-to-frame correction. -/
theorem slowCurveEndpointPolarAngleLiftCompatible (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          (∀ k : ℕ,
            orbit.endpointPolarAngleLift Clim (k + 1) -
                orbit.endpointPolarAngleLift Clim k ∈
              Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
            ∀ δ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
              (δ : Real.Angle) =
                  orbit.endpointPolarAngle Clim (k + 1) - orbit.endpointPolarAngle Clim k ↔
                δ = orbit.endpointPolarAngleLift Clim (k + 1) -
                  orbit.endpointPolarAngleLift Clim k) ∧
            ∀ j : ℕ,
              orbit.endpointPolarAngleLift Clim (2 * j) - orbit.frameAngle j =
                (EuclideanPlane.orientation.oangle (orbit.state j).lowVector
                  (orbit.endpoint (2 * j) - Clim)).toReal := by
  obtain ⟨ηGap, hηGap, hGap⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointPolarAngleGapExplicitBounds
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηCenter, hηCenter, Kcenter, hKcenter, hCenter⟩ :=
    DFP.TwoPhaseOrbit.slowCurveCenterTailUniformBound
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηGradient, hηGradient, gmin, hgmin, gmax, hgminmax,
      hGradient⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointGradientNormUniformBounds
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηValid, hηValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity
      p h h_invariant h_pJet h_hJet ηGraph hηGraph
  obtain ⟨ηFrame, hηFrame, hFrameRep⟩ :=
    DFP.TwoPhaseOrbit.slowCurveFrameAngleRepresentsLowVector
      p h h_invariant h_pJet h_hJet ηGraph hηGraph
  have hinitialAngle := DFP.TwoPhaseOrbit.slowCurveInitialGradientAngle_tendsto_zero
    p h h_pJet h_hJet
  have hangleBall : Metric.ball (0 : ℝ) (Real.pi / 16) ∈ 𝓝 0 :=
    Metric.ball_mem_nhds 0 (by positivity)
  have hangleEventually : ∀ᶠ ε in 𝓝 (0 : ℝ),
      |(EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (!₂[(1 : ℝ), p ε * ε ^ 2] : EuclideanSpace ℝ (Fin 2))).toReal| <
        Real.pi / 16 := by
    filter_upwards [hinitialAngle.eventually hangleBall] with ε hε
    simpa only [Real.dist_eq, sub_zero] using hε
  obtain ⟨r, hr, hrule⟩ := Metric.eventually_nhds_iff.mp hangleEventually
  let ηPi : ℝ := min (1 / 8 : ℝ) (Real.pi / 10)
  have hηPi : ηPi ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor
    · dsimp only [ηPi]
      exact lt_min (by norm_num) (by positivity)
    · exact (min_le_left (1 / 8 : ℝ) (Real.pi / 10)).trans_lt (by norm_num)
  let ρ : ℝ := gmin / 2
  have hρ : 0 < ρ := half_pos hgmin
  let ηTail : ℝ := ρ / (32 * Kcenter)
  have hηTail : 0 < ηTail := by
    dsimp only [ηTail]
    exact div_pos hρ (mul_pos (by norm_num) hKcenter)
  let εbar := min ηGap
    (min ηGraph (min ηPi
      (min ηCenter (min ηGradient (min ηValid
        (min ηFrame (min (r / 2) ηTail)))))))
  have hεbar : εbar ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor
    · exact lt_min hηGap.1 (lt_min hηGraph.1 (lt_min hηPi.1
        (lt_min hηCenter.1 (lt_min hηGradient.1 (lt_min hηValid.1
          (lt_min hηFrame.1 (lt_min (half_pos hr) hηTail)))))))
    · exact (min_le_left _ _).trans_lt hηGap.2
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Gap : ε₀ ∈ Set.Ioc 0 ηGap :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hε₀Pi : ε₀ ≤ ηPi :=
    hε₀.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hscale (j : ℕ) : (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
    have hx := hGraph ε₀ hε₀Graph j
    have hc := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hc' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hc
    have heq : (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
      simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using congrArg Prod.fst hc'
    rw [heq]
    exact hx.2
  intro Clim hClim
  have hgap := hGap ε₀ hε₀Gap Clim hClim
  constructor
  · intro k
    constructor
    · rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
      · have hb := (hgap.2 j 0)
        have he := (hscale j).1
        have hebar : (orbit.state j).ε < (1 / 4 : ℝ) :=
          lt_of_le_of_lt ((hscale j).2.trans hε₀Pi) hηPi.2
        rcases hb with ⟨hbLower, hbUpper⟩
        have hb' :
            (1 / 2 : ℝ) * (orbit.state j).ε ^ 2 ≤
              orbit.endpointPolarAngleLift Clim (2 * j) -
                orbit.endpointPolarAngleLift Clim (2 * j + 1) ∧
            orbit.endpointPolarAngleLift Clim (2 * j) -
                orbit.endpointPolarAngleLift Clim (2 * j + 1) ≤
              (5 / 2 : ℝ) * (orbit.state j).ε ^ 2 := by
          constructor
          · simpa only [orbit, Fin.val_zero, Nat.add_zero, Nat.succ_eq_add_one] using hbLower
          · simpa only [orbit, Fin.val_zero, Nat.add_zero, Nat.succ_eq_add_one] using hbUpper
        have hneg := hgap.1 (Nat.lt_succ_self (2 * j))
        have hneg' :
            orbit.endpointPolarAngleLift Clim (2 * j + 1) <
              orbit.endpointPolarAngleLift Clim (2 * j) := by
          simpa only [Nat.succ_eq_add_one] using hneg
        have hepi : (orbit.state j).ε ≤ Real.pi / 10 :=
          (hscale j).2.trans hε₀Pi |>.trans (min_le_right _ _)
        constructor <;> nlinarith [hb'.2, sq_nonneg ((orbit.state j).ε),
          Real.pi_pos]
      · have hb := (hgap.2 j 1)
        have he := (hscale j).1
        have hebar : (orbit.state j).ε < (1 / 4 : ℝ) :=
          lt_of_le_of_lt ((hscale j).2.trans hε₀Pi) hηPi.2
        rcases hb with ⟨hbLower, hbUpper⟩
        have hb' :
            (1 / 2 : ℝ) * (orbit.state j).ε ^ 2 ≤
              orbit.endpointPolarAngleLift Clim (2 * j + 1) -
                orbit.endpointPolarAngleLift Clim (2 * j + 2) ∧
            orbit.endpointPolarAngleLift Clim (2 * j + 1) -
                orbit.endpointPolarAngleLift Clim (2 * j + 2) ≤
              (5 / 2 : ℝ) * (orbit.state j).ε ^ 2 := by
          constructor
          · simpa only [orbit, Fin.val_one, Nat.succ_eq_add_one] using hbLower
          · simpa only [orbit, Fin.val_one, Nat.succ_eq_add_one] using hbUpper
        have hneg := hgap.1 (Nat.lt_succ_self (2 * j + 1))
        have hneg' :
            orbit.endpointPolarAngleLift Clim (2 * j + 2) <
              orbit.endpointPolarAngleLift Clim (2 * j + 1) := by
          simpa only [Nat.succ_eq_add_one] using hneg
        have hepi : (orbit.state j).ε ≤ Real.pi / 10 :=
          (hscale j).2.trans hε₀Pi |>.trans (min_le_right _ _)
        constructor <;> nlinarith [hb'.2, sq_nonneg ((orbit.state j).ε),
          Real.pi_pos]
    · intro δ hδ
      exact DFP.TwoPhaseOrbit.endpointPolarAngleLift_succ_sub_unique
        orbit Clim k δ hδ
  · -- The second conjunct uses the frame quotient interface and a principal-branch
    -- estimate assembled from the two center-tail perturbations.
    have hεbarCenter : εbar ≤ ηCenter := by
      dsimp only [εbar]
      calc
        min ηGap (min ηGraph (min ηPi (min ηCenter
            (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))))))
            ≤ min ηGraph (min ηPi (min ηCenter
                (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))))) :=
              min_le_right _ _
        _ ≤ min ηPi (min ηCenter
              (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail))))) :=
            min_le_right _ _
        _ ≤ min ηCenter
              (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))) :=
            min_le_right _ _
        _ ≤ ηCenter := min_le_left _ _
    have hεbarGradient : εbar ≤ ηGradient := by
      dsimp only [εbar]
      calc
        min ηGap (min ηGraph (min ηPi (min ηCenter
            (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))))))
            ≤ min ηGraph (min ηPi (min ηCenter
                (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))))) :=
              min_le_right _ _
        _ ≤ min ηPi (min ηCenter
              (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail))))) :=
            min_le_right _ _
        _ ≤ min ηCenter
              (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))) :=
            min_le_right _ _
        _ ≤ min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail))) :=
            min_le_right _ _
        _ ≤ ηGradient := min_le_left _ _
    have hεbarValid : εbar ≤ ηValid := by
      dsimp only [εbar]
      calc
        min ηGap (min ηGraph (min ηPi (min ηCenter
            (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))))))
            ≤ min ηGraph (min ηPi (min ηCenter
                (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))))) :=
              min_le_right _ _
        _ ≤ min ηPi (min ηCenter
              (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail))))) :=
            min_le_right _ _
        _ ≤ min ηCenter
              (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))) :=
            min_le_right _ _
        _ ≤ min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail))) :=
            min_le_right _ _
        _ ≤ min ηValid (min ηFrame (min (r / 2) ηTail)) := min_le_right _ _
        _ ≤ ηValid := min_le_left _ _
    have hεbarFrame : εbar ≤ ηFrame := by
      dsimp only [εbar]
      calc
        min ηGap (min ηGraph (min ηPi (min ηCenter
            (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))))))
            ≤ min ηGraph (min ηPi (min ηCenter
                (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))))) :=
              min_le_right _ _
        _ ≤ min ηPi (min ηCenter
              (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail))))) :=
            min_le_right _ _
        _ ≤ min ηCenter
              (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))) :=
            min_le_right _ _
        _ ≤ min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail))) :=
            min_le_right _ _
        _ ≤ min ηValid (min ηFrame (min (r / 2) ηTail)) := min_le_right _ _
        _ ≤ min ηFrame (min (r / 2) ηTail) := min_le_right _ _
        _ ≤ ηFrame := min_le_left _ _
    have hεbarRadius : εbar ≤ r / 2 := by
      dsimp only [εbar]
      calc
        min ηGap (min ηGraph (min ηPi (min ηCenter
            (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))))))
            ≤ min ηGraph (min ηPi (min ηCenter
                (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))))) :=
              min_le_right _ _
        _ ≤ min ηPi (min ηCenter
              (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail))))) :=
            min_le_right _ _
        _ ≤ min ηCenter
              (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))) :=
            min_le_right _ _
        _ ≤ min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail))) :=
            min_le_right _ _
        _ ≤ min ηValid (min ηFrame (min (r / 2) ηTail)) := min_le_right _ _
        _ ≤ min ηFrame (min (r / 2) ηTail) := min_le_right _ _
        _ ≤ min (r / 2) ηTail := min_le_right _ _
        _ ≤ r / 2 := min_le_left _ _
    have hεbarTail : εbar ≤ ηTail := by
      dsimp only [εbar]
      calc
        min ηGap (min ηGraph (min ηPi (min ηCenter
            (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))))))
            ≤ min ηGraph (min ηPi (min ηCenter
                (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))))) :=
              min_le_right _ _
        _ ≤ min ηPi (min ηCenter
              (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail))))) :=
            min_le_right _ _
        _ ≤ min ηCenter
              (min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail)))) :=
            min_le_right _ _
        _ ≤ min ηGradient (min ηValid (min ηFrame (min (r / 2) ηTail))) :=
            min_le_right _ _
        _ ≤ min ηValid (min ηFrame (min (r / 2) ηTail)) := min_le_right _ _
        _ ≤ min ηFrame (min (r / 2) ηTail) := min_le_right _ _
        _ ≤ min (r / 2) ηTail := min_le_right _ _
        _ ≤ ηTail := min_le_right _ _
    have hε₀Center : ε₀ ∈ Set.Ioc 0 ηCenter :=
      ⟨hε₀.1, hε₀.2.trans hεbarCenter⟩
    have hε₀Gradient : ε₀ ∈ Set.Ioc 0 ηGradient :=
      ⟨hε₀.1, hε₀.2.trans hεbarGradient⟩
    have hε₀Valid : ε₀ ∈ Set.Ioc 0 ηValid :=
      ⟨hε₀.1, hε₀.2.trans hεbarValid⟩
    have hε₀Frame : ε₀ ∈ Set.Ioc 0 ηFrame :=
      ⟨hε₀.1, hε₀.2.trans hεbarFrame⟩
    have hε₀Radius : ε₀ ≤ r / 2 := hε₀.2.trans hεbarRadius
    have hε₀Tail : ε₀ ≤ ηTail := hε₀.2.trans hεbarTail
    have hvalid (j : ℕ) : DFP.TwoPhaseOrbit.State.PhaseValidity (orbit.state j) := by
      simpa only [orbit] using hValid ε₀ hε₀Valid j
    have hgraphCoordinates (j : ℕ) :
        (orbit.state j).coordinates =
          ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
      obtain ⟨hcoordinateGraph, _⟩ := hGraph ε₀ hε₀Graph j
      calc
        (orbit.state j).coordinates =
            DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
              simpa only [orbit] using
                DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
        _ = ((DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
            p (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
            h (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) := hcoordinateGraph
        _ = ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
          have hc' : (orbit.state j).coordinates =
              DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
            simpa only [orbit] using
              DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
          have hcoord : (orbit.state j).ε =
              ((orbit.state j).coordinates).1 := by
            rw [DFP.TwoPhaseOrbit.State.coordinates_def]
          have heq : (orbit.state j).ε =
              (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 :=
            hcoord.trans (congrArg Prod.fst hc')
          rw [heq]
    have hgradientBounds (k : ℕ) :
        ‖orbit.endpointGradient k‖ ∈ Set.Icc gmin gmax := by
      simpa only [orbit] using hGradient ε₀ hε₀Gradient k
    have hgradientNe (k : ℕ) : orbit.endpointGradient k ≠ 0 := by
      exact norm_pos_iff.mp (hgmin.trans_le (hgradientBounds k).1)
    have htail (j : ℕ) : ‖(orbit.state j).center - Clim‖ +
        ‖(orbit.state j).middleCenter - Clim‖ ≤
          Kcenter * (orbit.state j).ε ^ 3 := by
      simpa only [orbit] using hCenter ε₀ hε₀Center Clim hClim j
    have hscaleUpper (j : ℕ) : (orbit.state j).ε ≤ ε₀ := (hscale j).2
    have htailSmall (j : ℕ) : Kcenter * (orbit.state j).ε ^ 3 ≤ ρ / 32 := by
      have hεone : (orbit.state j).ε ≤ 1 := by
        have hquarter : (1 / 4 : ℝ) ≤ 1 := by norm_num
        exact (hscale j).2.trans (hε₀.2.trans (hεbar.2.le.trans hquarter))
      have hpower : (orbit.state j).ε ^ 3 ≤ (orbit.state j).ε := by
        nlinarith [sq_nonneg ((orbit.state j).ε), (hscale j).1]
      calc
        Kcenter * (orbit.state j).ε ^ 3 ≤ Kcenter * (orbit.state j).ε :=
          mul_le_mul_of_nonneg_left hpower hKcenter.le
        _ ≤ Kcenter * ηTail :=
          mul_le_mul_of_nonneg_left ((hscale j).2.trans hε₀Tail) hKcenter.le
        _ = ρ / 32 := by
          dsimp only [ηTail]
          field_simp [hKcenter.ne']
    have hcenterEven (j : ℕ) : ‖(orbit.state j).center - Clim‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 :=
      (le_add_of_nonneg_right (norm_nonneg _)).trans (htail j)
    have hpointEven (j : ℕ) : orbit.endpoint (2 * j) - Clim =
        orbit.endpointGradient (2 * j) + ((orbit.state j).center - Clim) := by
      rw [DFP.TwoPhaseOrbit.endpoint_even,
        DFP.TwoPhaseOrbit.endpointGradient_even,
        DFP.TwoPhaseOrbit.State.center_def]
      abel
    have hperturbEven (j : ℕ) :
        ρ ≤ ‖orbit.endpoint (2 * j) - Clim‖ ∧
        |(EuclideanPlane.orientation.oangle (orbit.endpointGradient (2 * j))
          (orbit.endpoint (2 * j) - Clim)).toReal| ≤
            (Real.pi * Kcenter / ρ) * (orbit.state j).ε ^ 3 ∧
        |(EuclideanPlane.orientation.oangle (orbit.endpointGradient (2 * j))
          (orbit.endpoint (2 * j) - Clim)).toReal| < Real.pi / 16 := by
      rw [hpointEven]
      have hgradientLower : 2 * ρ ≤ ‖orbit.endpointGradient (2 * j)‖ := by
        dsimp only [ρ]
        nlinarith [(hgradientBounds (2 * j)).1]
      simpa only [div_eq_mul_inv, mul_assoc] using
        DFP.TwoPhaseOrbit.radialPerturbationAngleBounds
          (orbit.endpointGradient (2 * j))
          ((orbit.state j).center - Clim) ρ Kcenter (orbit.state j).ε hρ
          hgradientLower (hcenterEven j) (htailSmall j)
    have hradialNe (k : ℕ) : orbit.endpoint k - Clim ≠ 0 := by
      rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
      · exact norm_pos_iff.mp (hρ.trans_le (hperturbEven j).1)
      · have hcenterOdd : ‖(orbit.state j).middleCenter - Clim‖ ≤
            Kcenter * (orbit.state j).ε ^ 3 :=
          (le_add_of_nonneg_left (norm_nonneg _)).trans (htail j)
        have hpointOdd : orbit.endpoint (2 * j + 1) - Clim =
            orbit.endpointGradient (2 * j + 1) +
              ((orbit.state j).middleCenter - Clim) := by
          rw [DFP.TwoPhaseOrbit.endpoint_odd,
            DFP.TwoPhaseOrbit.endpointGradient_odd,
            DFP.TwoPhaseOrbit.State.middleCenter_def]
          abel
        rw [hpointOdd]
        have hgradientLower : 2 * ρ ≤ ‖orbit.endpointGradient (2 * j + 1)‖ := by
          dsimp only [ρ]
          nlinarith [(hgradientBounds (2 * j + 1)).1]
        have hpert := DFP.TwoPhaseOrbit.radialPerturbationAngleBounds
          (orbit.endpointGradient (2 * j + 1))
          ((orbit.state j).middleCenter - Clim) ρ Kcenter (orbit.state j).ε hρ
          hgradientLower hcenterOdd (htailSmall j)
        exact norm_pos_iff.mp (hρ.trans_le hpert.1)
    have hinitial : (orbit.state 0).lowVector =
        EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
      simpa only [orbit] using DFP.TwoPhaseOrbit.slowCurveInitialLowVector p h ε₀
    have hlow (j : ℕ) : (orbit.state j).lowVector ≠ 0 := by
      have hrot := hFrameRep ε₀ hε₀Frame j
      have hnorm : ‖(orbit.state j).lowVector‖ = 1 := by
        rw [hrot, hinitial]
        rw [(EuclideanPlane.rotation (orbit.frameAngle j)).norm_map]
        exact (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one 0
      exact norm_pos_iff.mp (by rw [hnorm]; norm_num)
    have hlowGradientSmall (j : ℕ) :
        |(EuclideanPlane.orientation.oangle (orbit.state j).lowVector
          (orbit.endpointGradient (2 * j))).toReal| < Real.pi / 16 := by
      have hangle := DFP.TwoPhaseOrbit.lowVector_gradientAngle_toReal_eq
        (orbit.state j) (hvalid j)
      have hpstate : (orbit.state j).p = p (orbit.state j).ε := by
        have hc := congrArg (fun z : ℝ × ℝ × ℝ ↦ z.2.1)
          (hgraphCoordinates j)
        simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using hc
      rw [DFP.TwoPhaseOrbit.endpointGradient_even, hangle, hpstate]
      have hdistance : dist (orbit.state j).ε 0 < r := by
        rw [Real.dist_eq, sub_zero, abs_of_pos (hscale j).1]
        exact ((hscale j).2.trans hε₀Radius).trans_lt (half_lt_self hr)
      have hbound := @hrule ((orbit.state j).ε) hdistance
      have hbasisCoord : EuclideanSpace.basisFun (Fin 2) ℝ 0 =
          (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) := by
        ext i
        fin_cases i <;> simp [EuclideanSpace.basisFun_apply]
      rw [hbasisCoord] at hbound
      exact hbound
    have hphysicalSmall (j : ℕ) :
        |(EuclideanPlane.orientation.oangle (orbit.state j).lowVector
          (orbit.endpoint (2 * j) - Clim)).toReal| < Real.pi / 8 := by
      exact DFP.TwoPhaseOrbit.oangle_toReal_add_small (orbit.state j).lowVector
        (orbit.endpointGradient (2 * j)) (orbit.endpoint (2 * j) - Clim)
        (hlow j) (hgradientNe (2 * j)) (hradialNe (2 * j))
        (hlowGradientSmall j) (hperturbEven j).2.2
    have hangle (j : ℕ) : EuclideanPlane.orientation.oangle
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) (orbit.state j).lowVector =
          (orbit.frameAngle j : Real.Angle) := by
      have hrot := hFrameRep ε₀ hε₀Frame j
      rw [hrot, hinitial]
      exact DFP.TwoPhaseOrbit.standardBasis_oangle_rotation _
    have hbridge := DFP.TwoPhaseOrbit.endpointPolarLiftFrameQuotient
      orbit Clim hinitial hlow hangle hradialNe
    have hgapSmall (k : ℕ) :
        |(orbit.endpointPolarAngle Clim (k + 1) -
          orbit.endpointPolarAngle Clim k).toReal| < Real.pi / 8 := by
      have hbound : |orbit.endpointPolarAngleLift Clim (k + 1) -
          orbit.endpointPolarAngleLift Clim k| < Real.pi / 8 := by
        rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
        · have hb := hgap.2 j 0
          have hnonneg : 0 ≤ orbit.endpointPolarAngleLift Clim (2 * j) -
              orbit.endpointPolarAngleLift Clim (2 * j + 1) := by
            have hblower : (1 / 2 : ℝ) * (orbit.state j).ε ^ 2 ≤
                orbit.endpointPolarAngleLift Clim (2 * j) -
                  orbit.endpointPolarAngleLift Clim (2 * j + 1) := by
              simpa only [orbit, Fin.val_zero, Nat.add_zero, Nat.succ_eq_add_one]
                using hb.1
            nlinarith [sq_nonneg ((orbit.state j).ε)]
          have habs : |orbit.endpointPolarAngleLift Clim (2 * j + 1) -
              orbit.endpointPolarAngleLift Clim (2 * j)| ≤
              (5 / 2 : ℝ) * (orbit.state j).ε ^ 2 := by
            calc
              _ = |-(orbit.endpointPolarAngleLift Clim (2 * j) -
                  orbit.endpointPolarAngleLift Clim (2 * j + 1))| := by
                congr 1; ring
              _ = orbit.endpointPolarAngleLift Clim (2 * j) -
                  orbit.endpointPolarAngleLift Clim (2 * j + 1) := by
                rw [abs_neg, abs_of_nonneg hnonneg]
              _ ≤ _ := by
                simpa only [orbit, Fin.val_zero, Nat.add_zero, Nat.succ_eq_add_one]
                  using hb.2
          have he : (orbit.state j).ε ≤ (1 / 8 : ℝ) :=
            (hscale j).2.trans (hε₀Pi.trans (min_le_left _ _))
          exact habs.trans_lt (by
            nlinarith [Real.pi_gt_three, sq_nonneg ((orbit.state j).ε),
              (hscale j).1])
        · have hb := hgap.2 j 1
          have hnonneg : 0 ≤ orbit.endpointPolarAngleLift Clim (2 * j + 1) -
              orbit.endpointPolarAngleLift Clim (2 * j + 2) := by
            have hblower : (1 / 2 : ℝ) * (orbit.state j).ε ^ 2 ≤
                orbit.endpointPolarAngleLift Clim (2 * j + 1) -
                  orbit.endpointPolarAngleLift Clim (2 * j + 2) := by
              simpa only [orbit, Fin.val_one, Nat.succ_eq_add_one] using hb.1
            nlinarith [sq_nonneg ((orbit.state j).ε)]
          have habs : |orbit.endpointPolarAngleLift Clim (2 * j + 2) -
              orbit.endpointPolarAngleLift Clim (2 * j + 1)| ≤
              (5 / 2 : ℝ) * (orbit.state j).ε ^ 2 := by
            calc
              _ = |-(orbit.endpointPolarAngleLift Clim (2 * j + 1) -
                  orbit.endpointPolarAngleLift Clim (2 * j + 2))| := by
                congr 1; ring
              _ = orbit.endpointPolarAngleLift Clim (2 * j + 1) -
                  orbit.endpointPolarAngleLift Clim (2 * j + 2) := by
                rw [abs_neg, abs_of_nonneg hnonneg]
              _ ≤ _ := by
                simpa only [orbit, Fin.val_one, Nat.succ_eq_add_one] using hb.2
          have he : (orbit.state j).ε ≤ (1 / 8 : ℝ) :=
            (hscale j).2.trans (hε₀Pi.trans (min_le_left _ _))
          exact habs.trans_lt (by
            nlinarith [Real.pi_gt_three, sq_nonneg ((orbit.state j).ε),
              (hscale j).1])
      calc
        |(orbit.endpointPolarAngle Clim (k + 1) -
            orbit.endpointPolarAngle Clim k).toReal| =
            |orbit.endpointPolarAngleLift Clim (k + 1) -
              orbit.endpointPolarAngleLift Clim k| := by
                rw [orbit.endpointPolarAngleLift_succ_sub Clim k]
        _ < Real.pi / 8 := hbound
    have hprincipal (j : ℕ) :
        (EuclideanPlane.orientation.oangle (orbit.state j).lowVector
            (orbit.endpoint (2 * j) - Clim)).toReal +
            (orbit.endpointPolarAngle Clim (2 * j + 1) -
              orbit.endpointPolarAngle Clim (2 * j)).toReal +
            (orbit.endpointPolarAngle Clim ((2 * j + 1) + 1) -
              orbit.endpointPolarAngle Clim (2 * j + 1)).toReal -
            (orbit.frameAngle (j + 1) - orbit.frameAngle j) ∈
          Set.Ioc (-Real.pi) Real.pi := by
      rcases abs_lt.mp (hphysicalSmall j) with ⟨haLower, haUpper⟩
      rcases abs_lt.mp (hgapSmall (2 * j)) with ⟨hbLower, hbUpper⟩
      rcases abs_lt.mp (hgapSmall (2 * j + 1)) with ⟨hcLower, hcUpper⟩
      have hd : orbit.frameAngle (j + 1) - orbit.frameAngle j ∈
          Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        rw [DFP.TwoPhaseOrbit.frameAngle_succ]
        convert (orbit.state j).angleIncrement_mem_interval using 1; ring
      constructor <;> linarith [Real.pi_pos, hd.1, hd.2]
    have hresult :=
      DFP.TwoPhaseOrbit.endpointPolarAngleLift_even_eq_frameAngle_add_correction_of_mem_Ioc
        orbit Clim hbridge.1 hbridge.2 hprincipal
    simpa only [orbit] using hresult
