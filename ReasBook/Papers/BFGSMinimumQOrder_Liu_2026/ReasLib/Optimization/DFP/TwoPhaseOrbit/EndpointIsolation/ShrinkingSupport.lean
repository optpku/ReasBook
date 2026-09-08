module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointIsolation.SlowCurve
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointClusterSet.Basic
public import ReasLib.Topology.MetricSpace.SupportDistance
import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointDistance
import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleAsymptotics
import Mathlib.Tactic.NormNum

public section

noncomputable section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoLeg.SlowCurve

/-- The physical state scale along every sufficiently small orbit carried by
an invariant slow curve tends to zero. -/
theorem stateScaleTendstoZero (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) := by
  obtain ⟨εbar, hεbar, hscale⟩ := curve.scaleTendstoZero
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀)).1 := by
    have hraw := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates
      curve.shape curve.high ε₀ j
    have hraw' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀) := by
      simpa only [orbit] using hraw
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hraw'
  exact (hscale ε₀ hε₀).congr'
    (Eventually.of_forall (fun j ↦ (hcoord j).symm))

/-- Along a sufficiently small invariant slow curve, interpolation radii and
endpoint distances to the limiting circle both tend to zero. -/
theorem interpolationRadiusAndLimitCircleDistanceTendstoZero
    (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              Tendsto (fun k : ℕ ↦ orbit.interpolationRadius Clim Glim k)
                  atTop (𝓝 0) ∧
                Tendsto (fun k : ℕ ↦ Metric.infDist (orbit.endpoint k)
                  (DFP.TwoPhaseOrbit.limitCircle Clim Glim)) atTop (𝓝 0) := by
  obtain ⟨ηRadius, hηRadius, _, _, cUpper, _, hRadius⟩ :=
    curve.interpolationRadiusUniformBounds
  obtain ⟨ηDistance, hηDistance, hDistance⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointLimitCircleDistanceEquivalent
      curve.shape curve.high curve.isInvariant
        curve.shapeRemainder curve.highRemainder
  obtain ⟨ηScale, hηScale, hScale⟩ := curve.stateScaleTendstoZero
  let εbar := min ηRadius (min ηDistance ηScale)
  have hεbarPos : 0 < εbar :=
    lt_min hηRadius.1 (lt_min hηDistance.1 hηScale.1)
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηRadius.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεRadius : ε₀ ∈ Set.Ioc 0 ηRadius :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεDistance : ε₀ ∈ Set.Ioc 0 ηDistance :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεScale : ε₀ ∈ Set.Ioc 0 ηScale :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  intro Clim hClim Glim hGlim hGlimTendsto
  have hRadiusData :=
    hRadius ε₀ hεRadius Clim hClim Glim hGlim hGlimTendsto
  have hDistanceEq :
      (fun k : ℕ ↦ Metric.infDist (orbit.endpoint k)
          (DFP.TwoPhaseOrbit.limitCircle Clim Glim)) ~[atTop]
        (fun k : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state (k / 2)).ε) := by
    simpa only [orbit] using
      hDistance ε₀ hεDistance Clim hClim Glim hGlim hGlimTendsto
  have hScaleZero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε)
      atTop (𝓝 0) := by
    simpa only [orbit] using hScale ε₀ hεScale
  have hFlatScaleZero : Tendsto (fun k : ℕ ↦ (orbit.state (k / 2)).ε)
      atTop (𝓝 0) :=
    hScaleZero.comp (Nat.tendsto_div_const_atTop (by norm_num))
  have hEndpointRadiusZero : Tendsto
      (fun k : ℕ ↦ orbit.endpointRadius k) atTop (𝓝 0) := by
    simpa only [DFP.TwoPhaseOrbit.endpointRadius_def,
      zero_pow (by norm_num : 2 ≠ 0)] using hFlatScaleZero.pow 2
  have hRadiusUpperZero : Tendsto
      (fun k : ℕ ↦ cUpper * orbit.endpointRadius k) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hEndpointRadiusZero : Tendsto
        (fun k : ℕ ↦ cUpper * orbit.endpointRadius k) atTop (𝓝 (cUpper * 0)))
  have hRadiusZero : Tendsto
      (fun k : ℕ ↦ orbit.interpolationRadius Clim Glim k) atTop (𝓝 0) := by
    exact squeeze_zero
      (fun k ↦ DFP.TwoPhaseOrbit.interpolationRadius_nonneg orbit Clim Glim k)
      (fun k ↦ (hRadiusData k).2) hRadiusUpperZero
  have hDistanceModelZero : Tendsto
      (fun k : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state (k / 2)).ε)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hFlatScaleZero : Tendsto
        (fun k : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state (k / 2)).ε)
          atTop (𝓝 (((13 / 3 : ℝ) * Glim) * 0)))
  exact ⟨hRadiusZero, hDistanceEq.symm.tendsto_nhds hDistanceModelZero⟩

/-- Along a sufficiently small invariant slow curve, interpolation radii tend
to zero. -/
theorem interpolationRadiusTendstoZero (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              Tendsto (fun k : ℕ ↦ orbit.interpolationRadius Clim Glim k)
                atTop (𝓝 0) := by
  obtain ⟨εbar, hεbar, hboth⟩ :=
    interpolationRadiusAndLimitCircleDistanceTendstoZero curve
  exact ⟨εbar, hεbar, fun ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto ↦
    (hboth ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto).1⟩

/-- Every cluster point of the endpoints of a sufficiently small invariant
slow-curve orbit belongs to its limiting circle. -/
theorem endpointClusterPt_mem_limitCircle (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ x, MapClusterPt x atTop orbit.endpoint →
                x ∈ DFP.TwoPhaseOrbit.limitCircle Clim Glim := by
  obtain ⟨εbar, hεbar, hboth⟩ :=
    interpolationRadiusAndLimitCircleDistanceTendstoZero curve
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro Clim hClim Glim hGlim hGlimTendsto x hx
  have hDistanceZero :=
    (hboth ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto).2
  exact DFP.TwoPhaseOrbit.mapClusterPt_mem_of_tendsto_infDist
    (DFP.TwoPhaseOrbit.isClosed_limitCircle Clim Glim hGlim)
    (DFP.TwoPhaseOrbit.limitCircle_nonempty Clim Glim hGlim)
    hx hDistanceZero

/-- Along a sufficiently small invariant slow curve, every interpolation
radius is strictly positive. -/
theorem interpolationRadius_pos (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ k : ℕ, 0 < orbit.interpolationRadius Clim Glim k := by
  obtain ⟨ηRadius, hηRadius, cLower, hcLower, _, _, hRadius⟩ :=
    curve.interpolationRadiusUniformBounds
  obtain ⟨ηPos, hηPos, hPos⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitPos
      curve.shape curve.high curve.isInvariant
        curve.shapeRemainder curve.highRemainder
  let εbar := min ηRadius ηPos
  have hεbarPos : 0 < εbar := lt_min hηRadius.1 hηPos
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηRadius.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεRadius : ε₀ ∈ Set.Ioc 0 ηRadius :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεPos : ε₀ ∈ Set.Ioc 0 ηPos :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  have hcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀)).1 := by
    have hraw := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates
      curve.shape curve.high ε₀ j
    have hraw' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀) := by
      simpa only [orbit] using hraw
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hraw'
  have hscalePos (j : ℕ) : 0 < (orbit.state j).ε := by
    rw [hcoord j]
    exact (hPos ε₀ hεPos j).1
  intro Clim hClim Glim hGlim hGlimTendsto k
  have hLower :=
    (hRadius ε₀ hεRadius Clim hClim Glim hGlim hGlimTendsto k).1
  exact (mul_pos hcLower (by
    rw [DFP.TwoPhaseOrbit.endpointRadius_def]
    exact pow_pos (hscalePos (k / 2)) 2)).trans_le hLower

/-- Along a sufficiently small invariant slow curve, every positive closed
thickening of the limiting circle eventually contains every interpolation
ball. -/
theorem interpolationBallsEventuallyNearLimitCircle
    (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ δ > 0, ∀ᶠ k : ℕ in atTop,
                Metric.closedBall (orbit.endpoint k)
                    (orbit.interpolationRadius Clim Glim k) ⊆
                  Metric.cthickening δ
                    (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
  obtain ⟨εbar, hεbar, hboth⟩ :=
    interpolationRadiusAndLimitCircleDistanceTendstoZero curve
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  intro Clim hClim Glim hGlim hGlimTendsto δ hδ
  obtain ⟨hRadiusZero, hDistanceZero⟩ :=
    hboth ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto
  exact Metric.eventually_closedBall_subset_cthickening_of_tendsto
    (DFP.TwoPhaseOrbit.limitCircle Clim Glim) orbit.endpoint
    (fun k ↦ orbit.interpolationRadius Clim Glim k)
    (DFP.TwoPhaseOrbit.isClosed_limitCircle Clim Glim hGlim)
    (DFP.TwoPhaseOrbit.limitCircle_nonempty Clim Glim hGlim)
    hDistanceZero hRadiusZero δ hδ

/-- Along a sufficiently small invariant slow curve, interpolation radius is
big-O of endpoint radius. -/
theorem interpolationRadius_isBigO_endpointRadius
    (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              (fun k : ℕ ↦ orbit.interpolationRadius Clim Glim k) =O[atTop]
                orbit.endpointRadius := by
  obtain ⟨εbar, hεbar, _, _, cUpper, hcUpper, hRadius⟩ :=
    curve.interpolationRadiusUniformBounds
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  intro Clim hClim Glim hGlim hGlimTendsto
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨cUpper, Eventually.of_forall ?_⟩
  intro k
  have hBounds := hRadius ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto k
  have hRadiusNonneg : 0 ≤ orbit.interpolationRadius Clim Glim k :=
    DFP.TwoPhaseOrbit.interpolationRadius_nonneg orbit Clim Glim k
  have hEndpointRadiusNonneg : 0 ≤ orbit.endpointRadius k := by
    rw [DFP.TwoPhaseOrbit.endpointRadius_def]
    exact sq_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hRadiusNonneg, abs_of_nonneg hEndpointRadiusNonneg]
  exact hBounds.2

end DFP.TwoLeg.SlowCurve
