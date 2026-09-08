module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleAsymptotics
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeLimit
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeTail
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterTail
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterConvergence
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.FrameAngleDivergence
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointClusterSet

public section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit

/-- A sufficiently small invariant slow-curve orbit has the canonical scale,
amplitude, center, winding, and endpoint cluster-set asymptotics. -/
theorem slowCurveScalarAsymptotics (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∃ Glim > 0, ∃ Clim : EuclideanSpace ℝ (Fin 2),
        (fun j : ℕ ↦ (orbit.state j).ε) ~[atTop]
          (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) ∧
        Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) ∧
        (fun j : ℕ ↦ (orbit.state j).amplitude - Glim) ~[atTop]
          (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε) ∧
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) ∧
        (fun j : ℕ ↦ ‖(orbit.state j).center - Clim‖) =O[atTop]
          (fun j : ℕ ↦ (orbit.state j).ε ^ 3) ∧
        (fun j : ℕ ↦ ‖(orbit.state j).middleCenter - Clim‖) =O[atTop]
          (fun j : ℕ ↦ (orbit.state j).ε ^ 3) ∧
        Tendsto orbit.frameAngle atTop atBot ∧
        {x : EuclideanSpace ℝ (Fin 2) | MapClusterPt x atTop orbit.endpoint} =
          DFP.TwoPhaseOrbit.limitCircle Clim Glim := by
  obtain ⟨εbarScale, hεbarScale, hScale⟩ :=
    DFP.TwoLeg.slowCurveScaleAsymptotic p h h_invariant h_pJet h_hJet
  obtain ⟨εbarAmplitude, hεbarAmplitude, hAmplitude⟩ :=
    slowCurveAmplitudeExistsPositiveLimit p h h_invariant h_pJet h_hJet
  obtain ⟨εbarAmplitudeTail, hεbarAmplitudeTail, hAmplitudeTail⟩ :=
    slowCurveAmplitudeTailEquivalent p h h_invariant h_pJet h_hJet
  obtain ⟨εbarCenter, hεbarCenter, hCenter⟩ :=
    slowCurveCenterTendsto p h h_invariant h_pJet h_hJet
  obtain ⟨εbarBoundary, hεbarBoundary, hBoundary⟩ :=
    slowCurveBoundaryCenterTailIsBigO p h h_invariant h_pJet h_hJet
  obtain ⟨εbarMiddle, hεbarMiddle, hMiddle⟩ :=
    slowCurveMiddleCenterTailIsBigO p h h_invariant h_pJet h_hJet
  obtain ⟨εbarFrame, hεbarFrame, hFrame⟩ :=
    slowCurveFrameAngleTendstoAtBot p h h_invariant h_pJet h_hJet
  obtain ⟨εbarCluster, hεbarCluster, hCluster⟩ :=
    slowCurveEndpointClusterSet_eq_limitCircle p h h_invariant h_pJet h_hJet
  let εbar := min (min (min εbarScale εbarAmplitude) εbarAmplitudeTail)
    (min (min εbarCenter εbarBoundary)
      (min (min εbarMiddle εbarFrame) εbarCluster))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min (lt_min (lt_min hεbarScale hεbarAmplitude) hεbarAmplitudeTail)
      (lt_min (lt_min hεbarCenter.1 hεbarBoundary.1)
        (lt_min (lt_min hεbarMiddle.1 hεbarFrame.1) hεbarCluster.1))
  have hεbarLt : εbar < (1 / 4 : ℝ) := by
    have hle : εbar ≤ εbarCenter := by
      dsimp only [εbar]
      exact (min_le_right _ _).trans
        ((min_le_left _ _).trans (min_le_left _ _))
    exact hle.trans_lt hεbarCenter.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεbar_le_scale : εbar ≤ εbarScale := by
    dsimp only [εbar]
    exact (min_le_left _ _).trans
      ((min_le_left _ _).trans (min_le_left _ _))
  have hεbar_le_amplitude : εbar ≤ εbarAmplitude := by
    dsimp only [εbar]
    exact (min_le_left _ _).trans
      ((min_le_left _ _).trans (min_le_right _ _))
  have hεbar_le_amplitudeTail : εbar ≤ εbarAmplitudeTail := by
    dsimp only [εbar]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hεbar_le_center : εbar ≤ εbarCenter := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_left _ _).trans (min_le_left _ _))
  have hεbar_le_boundary : εbar ≤ εbarBoundary := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_left _ _).trans (min_le_right _ _))
  have hεbar_le_middle : εbar ≤ εbarMiddle := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_left _ _).trans (min_le_left _ _)))
  have hεbar_le_frame : εbar ≤ εbarFrame := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_left _ _).trans (min_le_right _ _)))
  have hεbar_le_cluster : εbar ≤ εbarCluster := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  have hε₀Scale : ε₀ ∈ Set.Ioc 0 εbarScale :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_scale⟩
  have hε₀Amplitude : ε₀ ∈ Set.Ioc 0 εbarAmplitude :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_amplitude⟩
  have hε₀AmplitudeTail : ε₀ ∈ Set.Ioc 0 εbarAmplitudeTail :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_amplitudeTail⟩
  have hε₀Center : ε₀ ∈ Set.Ioc 0 εbarCenter :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_center⟩
  have hε₀Boundary : ε₀ ∈ Set.Ioc 0 εbarBoundary :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_boundary⟩
  have hε₀Middle : ε₀ ∈ Set.Ioc 0 εbarMiddle :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_middle⟩
  have hε₀Frame : ε₀ ∈ Set.Ioc 0 εbarFrame :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_frame⟩
  have hε₀Cluster : ε₀ ∈ Set.Ioc 0 εbarCluster :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_cluster⟩
  have hεcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hcoord' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hcoord
    simpa only [State.coordinates_def] using congrArg Prod.fst hcoord'
  have hScaleOrbit :
      (fun j : ℕ ↦ (orbit.state j).ε) ~[atTop]
        (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) := by
    simpa only [hεcoord] using hScale ε₀ hε₀Scale
  obtain ⟨Glim, hGlim, hGlimTendsto⟩ := by
    simpa only [orbit] using hAmplitude ε₀ hε₀Amplitude
  obtain ⟨Clim, hClim⟩ := by
    simpa only [orbit] using hCenter ε₀ hε₀Center
  have hAmplitudeTailOrbit :
      (fun j : ℕ ↦ (orbit.state j).amplitude - Glim) ~[atTop]
        (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε) := by
    simpa only [orbit] using
      hAmplitudeTail ε₀ hε₀AmplitudeTail Glim hGlim hGlimTendsto
  have hBoundaryOrbit :
      (fun j : ℕ ↦ ‖(orbit.state j).center - Clim‖) =O[atTop]
        (fun j : ℕ ↦ (orbit.state j).ε ^ 3) := by
    simpa only [orbit] using hBoundary ε₀ hε₀Boundary Clim hClim
  have hMiddleOrbit :
      (fun j : ℕ ↦ ‖(orbit.state j).middleCenter - Clim‖) =O[atTop]
        (fun j : ℕ ↦ (orbit.state j).ε ^ 3) := by
    simpa only [orbit] using hMiddle ε₀ hε₀Middle Clim hClim
  have hFrameOrbit : Tendsto orbit.frameAngle atTop atBot := by
    simpa only [orbit] using hFrame ε₀ hε₀Frame
  have hClusterOrbit :
      {x : EuclideanSpace ℝ (Fin 2) | MapClusterPt x atTop orbit.endpoint} =
        DFP.TwoPhaseOrbit.limitCircle Clim Glim := by
    simpa only [orbit] using
      hCluster ε₀ hε₀Cluster Clim hClim Glim hGlim hGlimTendsto
  refine ⟨Glim, hGlim, Clim, ?_⟩
  simpa only [orbit] using
    (show
      (fun j : ℕ ↦ (orbit.state j).ε) ~[atTop]
          (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) ∧
        Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) ∧
        (fun j : ℕ ↦ (orbit.state j).amplitude - Glim) ~[atTop]
          (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε) ∧
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) ∧
        (fun j : ℕ ↦ ‖(orbit.state j).center - Clim‖) =O[atTop]
          (fun j : ℕ ↦ (orbit.state j).ε ^ 3) ∧
        (fun j : ℕ ↦ ‖(orbit.state j).middleCenter - Clim‖) =O[atTop]
          (fun j : ℕ ↦ (orbit.state j).ε ^ 3) ∧
        Tendsto orbit.frameAngle atTop atBot ∧
        {x : EuclideanSpace ℝ (Fin 2) | MapClusterPt x atTop orbit.endpoint} =
          DFP.TwoPhaseOrbit.limitCircle Clim Glim
      from ⟨hScaleOrbit, hGlimTendsto, hAmplitudeTailOrbit, hClim,
        hBoundaryOrbit, hMiddleOrbit, hFrameOrbit, hClusterOrbit⟩)

end DFP.TwoPhaseOrbit
