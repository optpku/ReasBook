module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.InvariantGraph
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointIsolation
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointCorrection
import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.Positivity
import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointDistance
import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSeparation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Endpoint isolation along invariant slow curves

This module packages the uniform endpoint-isolation consequences of an
invariant fifth-order slow curve.  The underlying metric and orbit-level
facts remain in `Metric.Isolation` and `TwoPhaseOrbit.EndpointIsolation`;
only the slow-curve quantifiers and asymptotic inputs live here.
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.SlowCurve

/-- Along a sufficiently small invariant slow curve, every interpolation
radius is bounded above and below by positive multiples of the corresponding
endpoint radius. -/
theorem interpolationRadiusUniformBounds (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cLower > 0, ∃ cUpper > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ k : ℕ, orbit.interpolationRadius Clim Glim k ∈ Set.Icc
                  (cLower * orbit.endpointRadius k)
                  (cUpper * orbit.endpointRadius k) := by
  obtain ⟨ηSep, hηSep, cStar, hcStar, hSep⟩ :=
    DFP.TwoPhaseOrbit.slowCurveUniformEndpointSeparation
      curve.shape curve.high curve.isInvariant
      curve.shapeRemainder curve.highRemainder
  obtain ⟨ηInj, hηInj, hInj⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpoint_injective
      curve.shape curve.high curve.isInvariant
      curve.shapeRemainder curve.highRemainder
  obtain ⟨ηAdj, hηAdj, C, hC, hAdj⟩ :=
    adjacentEndpointDistanceUpper curve
  let εbar := min ηSep (min ηInj ηAdj)
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηSep.1 (lt_min hηInj.1 hηAdj.1)
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηSep.2
  have hfourPos : (0 : ℝ) < 4 := by
    norm_num
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩,
    cStar / 4, div_pos hcStar hfourPos,
    C / 4, div_pos hC hfourPos, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεSep : ε₀ ∈ Set.Ioc 0 ηSep := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    dsimp only [εbar]
    exact min_le_left _ _
  have hεInj : ε₀ ∈ Set.Ioc 0 ηInj := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεAdj : ε₀ ∈ Set.Ioc 0 ηAdj := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_right _ _)
  intro Clim hClim Glim hGlim hGlimTendsto k
  have hSepData := hSep ε₀ hεSep Clim hClim Glim hGlim hGlimTendsto k
  have hInjData := hInj ε₀ hεInj Clim hClim Glim hGlim hGlimTendsto
  have hAdjData := hAdj ε₀ hεAdj k
  have hSepRadius : cStar * orbit.endpointRadius k ≤
      orbit.isolationDistance Clim Glim k := by
    rw [DFP.TwoPhaseOrbit.endpointRadius_def,
      DFP.TwoPhaseOrbit.isolationDistance_def]
    exact hSepData
  have hAdjRadius : dist (orbit.endpoint k) (orbit.endpoint (k + 1)) ≤
      C * orbit.endpointRadius k := hAdjData
  have hnextNe : orbit.endpoint (k + 1) ≠ orbit.endpoint k :=
    (hInjData.ne (Nat.ne_of_lt (Nat.lt_succ_self k))).symm
  have hnextMem : orbit.endpoint (k + 1) ∈
      orbit.closedSetCandidate Clim Glim \ {orbit.endpoint k} := by
    constructor
    · exact DFP.TwoPhaseOrbit.mem_closedSetCandidate.mpr
        (Or.inr ⟨k + 1, rfl⟩)
    · simpa only [Set.mem_singleton_iff] using hnextNe
  have hisolationUpper : orbit.isolationDistance Clim Glim k ≤
      dist (orbit.endpoint k) (orbit.endpoint (k + 1)) := by
    rw [DFP.TwoPhaseOrbit.isolationDistance_def]
    exact Metric.infDist_le_dist_of_mem hnextMem
  rw [DFP.TwoPhaseOrbit.interpolationRadius_eq_isolationDistance_div,
    Set.mem_Icc]
  constructor
  · calc
      cStar / 4 * orbit.endpointRadius k =
          (cStar * orbit.endpointRadius k) / 4 := by ring
      _ ≤ orbit.isolationDistance Clim Glim k / 4 :=
        div_le_div_of_nonneg_right hSepRadius hfourPos.le
  · calc
      orbit.isolationDistance Clim Glim k / 4 ≤
          dist (orbit.endpoint k) (orbit.endpoint (k + 1)) / 4 :=
        div_le_div_of_nonneg_right hisolationUpper hfourPos.le
      _ ≤ (C * orbit.endpointRadius k) / 4 :=
        div_le_div_of_nonneg_right hAdjRadius hfourPos.le
      _ = C / 4 * orbit.endpointRadius k := by ring

/-- Along a sufficiently small invariant slow curve, the closed interpolation
balls form a pairwise-disjoint family. -/
theorem pairwiseDisjointInterpolationClosedBalls (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              Set.univ.PairwiseDisjoint (fun k : ℕ ↦
                Metric.closedBall (orbit.endpoint k)
                  (orbit.interpolationRadius Clim Glim k)) := by
  obtain ⟨εbar, hεbar, hInj⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpoint_injective
      curve.shape curve.high curve.isInvariant
      curve.shapeRemainder curve.highRemainder
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  intro Clim hClim Glim hGlim hGlimTendsto
  have hInjData := hInj ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto
  exact DFP.TwoPhaseOrbit.pairwiseDisjoint_interpolationClosedBall
    orbit Clim Glim hInjData

/-- Along a sufficiently small invariant slow curve, every closed
interpolation ball is disjoint from the limiting circle. -/
theorem interpolationClosedBallDisjointLimitCircle
    (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ k : ℕ, Disjoint
                (Metric.closedBall (orbit.endpoint k)
                  (orbit.interpolationRadius Clim Glim k))
                (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
  obtain ⟨ηSep, hηSep, cStar, hcStar, hSep⟩ :=
    DFP.TwoPhaseOrbit.slowCurveUniformEndpointSeparation
      curve.shape curve.high curve.isInvariant
      curve.shapeRemainder curve.highRemainder
  obtain ⟨ηCircle, hηCircle, cCircle, hcCircle, hCircle⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointLimitCircleInfDistUniformLower
      curve.shape curve.high curve.isInvariant
      curve.shapeRemainder curve.highRemainder
  obtain ⟨ηPos, hηPos, hPos⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitPos
      curve.shape curve.high curve.isInvariant
      curve.shapeRemainder curve.highRemainder
  let εbar := min ηSep (min ηCircle ηPos)
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηSep.1 (lt_min hηCircle.1 hηPos)
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηSep.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεSep : ε₀ ∈ Set.Ioc 0 ηSep := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    dsimp only [εbar]
    exact min_le_left _ _
  have hεCircle : ε₀ ∈ Set.Ioc 0 ηCircle := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεPos : ε₀ ∈ Set.Ioc 0 ηPos := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hcoordinate (j : ℕ) : (orbit.state j).ε =
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
    rw [hcoordinate j]
    exact (hPos ε₀ hεPos j).1
  intro Clim hClim Glim hGlim hGlimTendsto k
  have hSepData := hSep ε₀ hεSep Clim hClim Glim hGlim hGlimTendsto k
  have hCircleData :=
    hCircle ε₀ hεCircle Clim hClim Glim hGlim hGlimTendsto k
  have hisolationPos : 0 < orbit.isolationDistance Clim Glim k := by
    rw [DFP.TwoPhaseOrbit.isolationDistance_def]
    exact (mul_pos hcStar (pow_pos (hscalePos (k / 2)) 2)).trans_le hSepData
  have hcirclePos : 0 < Metric.infDist (orbit.endpoint k)
      (DFP.TwoPhaseOrbit.limitCircle Clim Glim) :=
    (mul_pos hcCircle (pow_pos (hscalePos (k / 2)) 2)).trans_le hCircleData
  have hendpointNotCircle : orbit.endpoint k ∉
      DFP.TwoPhaseOrbit.limitCircle Clim Glim := by
    intro hk
    have hzero : Metric.infDist (orbit.endpoint k)
        (DFP.TwoPhaseOrbit.limitCircle Clim Glim) = 0 :=
      Metric.infDist_zero_of_mem hk
    exact (ne_of_gt hcirclePos) hzero
  exact DFP.TwoPhaseOrbit.interpolationClosedBall_disjoint_limitCircle
    orbit Clim Glim k hisolationPos hendpointNotCircle

end DFP.TwoLeg.SlowCurve
