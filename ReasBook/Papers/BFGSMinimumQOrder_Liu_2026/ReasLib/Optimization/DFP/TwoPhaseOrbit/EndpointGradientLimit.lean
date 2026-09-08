module

import ReasLib.Analysis.Asymptotics.Interleave
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.OrbitBounds
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleSummability
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeLimit
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientLimit.UniformBounds

public section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit

/-- For every sufficiently small canonical slow-curve orbit, the norms of the
gradients along the full endpoint sequence converge to a strictly positive limit. -/
theorem slowCurveEndpointGradientNormTendsto (p h : ℝ → ℝ)
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
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∃ Glim > 0,
        Tendsto (fun k : ℕ ↦ ‖orbit.endpointGradient k‖) atTop (𝓝 Glim) := by
  obtain ⟨εbarAmplitude, hεbarAmplitude, hAmplitude⟩ :=
    slowCurveAmplitudeExistsPositiveLimit p h h_invariant h_pJet h_hJet
  have honeEighth : (1 / 8 : ℝ) ∈ Set.Ioo 0 (1 / 4) := by
    norm_num
  obtain ⟨εbarValid, hεbarValid, hValid⟩ :=
    ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet (1 / 8) honeEighth
  obtain ⟨εbarSum, hεbarSum, hSum⟩ :=
    DFP.TwoLeg.slowCurveScaleFourthPowerSummable p h h_invariant h_pJet h_hJet
  obtain ⟨εbarGraph, hεbarGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min (min εbarAmplitude εbarValid) (min εbarSum εbarGraph)
  have hεbar_pos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min (lt_min hεbarAmplitude hεbarValid.1)
      (lt_min hεbarSum hεbarGraph.1)
  refine ⟨εbar, hεbar_pos, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := ofSlowCurve p h ε₀
  have hεbar_le_amplitude : εbar ≤ εbarAmplitude := by
    dsimp only [εbar]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hεbar_le_valid : εbar ≤ εbarValid := by
    dsimp only [εbar]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hεbar_le_sum : εbar ≤ εbarSum := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεbar_le_graph : εbar ≤ εbarGraph := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hε₀Amplitude : ε₀ ∈ Set.Ioc 0 εbarAmplitude :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_amplitude⟩
  have hε₀Valid : ε₀ ∈ Set.Ioc 0 εbarValid :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_valid⟩
  have hε₀Sum : ε₀ ∈ Set.Ioc 0 εbarSum :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_sum⟩
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 εbarGraph :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_graph⟩
  have hvalid (j : ℕ) : State.PhaseValidity (orbit.state j) := by
    simpa only [orbit] using hValid ε₀ hε₀Valid j
  have hεcoord (j : ℕ) :
      (orbit.state j).ε = (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hcoordinates := ofSlowCurve_coordinates p h ε₀ j
    have hcoordinates' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hcoordinates
    have hfst := congrArg Prod.fst hcoordinates'
    simpa only [State.coordinates_def] using hfst
  have hgraphCoordinates (j : ℕ) :
      (orbit.state j).coordinates =
        ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
    obtain ⟨hcoordinateGraph, _⟩ := hGraph ε₀ hε₀Graph j
    calc
      (orbit.state j).coordinates =
          DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
            simpa only [orbit] using ofSlowCurve_coordinates p h ε₀ j
      _ = ((DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          p (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          h (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) := hcoordinateGraph
      _ = ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
        rw [hεcoord j]
  let scaleFourth : ℕ → ℝ := fun j ↦ (orbit.state j).ε ^ 4
  have hscaleFourthSummable : Summable scaleFourth := by
    have hsummable := hSum ε₀ hε₀Sum
    simpa only [scaleFourth, hεcoord] using hsummable
  have hscaleFourthZero : Tendsto scaleFourth atTop (𝓝 0) :=
    hscaleFourthSummable.tendsto_atTop_zero
  have hscaleZero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) := by
    have hquarter : (0 : ℝ) < 1 / 4 := by
      norm_num
    have hfour_ne : 4 ≠ 0 := by
      norm_num
    have hroot := hscaleFourthZero.rpow_const_nhds_zero hquarter
    have hrootEq (j : ℕ) :
        scaleFourth j ^ (1 / 4 : ℝ) = (orbit.state j).ε := by
      have hidentity := Real.pow_rpow_inv_natCast (hvalid j).ε_pos.le hfour_ne
      dsimp only [scaleFourth]
      convert hidentity using 1
      norm_num
    exact hroot.congr' (Eventually.of_forall hrootEq)
  obtain ⟨Glim, hGlim, hAmplitudeTendstoRaw⟩ := hAmplitude ε₀ hε₀Amplitude
  have hAmplitudeTendsto :
      Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) := by
    simpa only [orbit] using hAmplitudeTendstoRaw
  let graph := DFP.TwoLeg.SlowGraph.ofAsymptotics p h h_pJet h_hJet
  have hGraphNorms := graph.gradientNorms_tendsto
  have hInitialNormalized : Tendsto
      (fun j : ℕ ↦
        (DFP.TwoLeg.observableMap
          ((orbit.state j).ε, p (orbit.state j).ε,
            h (orbit.state j).ε)).initialGradientNorm)
      atTop (𝓝 1) := by
    have ht := (continuous_fst.tendsto ((1, 1) : ℝ × ℝ)).comp
      (hGraphNorms.comp hscaleZero)
    simpa only [Function.comp_def, graph, DFP.TwoLeg.SlowGraph.path_apply,
      DFP.TwoLeg.SlowGraph.ofAsymptotics_shape,
      DFP.TwoLeg.SlowGraph.ofAsymptotics_high] using ht
  have hIntermediateNormalized : Tendsto
      (fun j : ℕ ↦
        (DFP.TwoLeg.observableMap
          ((orbit.state j).ε, p (orbit.state j).ε,
            h (orbit.state j).ε)).intermediateGradientNorm)
      atTop (𝓝 1) := by
    have ht := (continuous_snd.tendsto ((1, 1) : ℝ × ℝ)).comp
      (hGraphNorms.comp hscaleZero)
    simpa only [Function.comp_def, graph, DFP.TwoLeg.SlowGraph.path_apply,
      DFP.TwoLeg.SlowGraph.ofAsymptotics_shape,
      DFP.TwoLeg.SlowGraph.ofAsymptotics_high] using ht
  have hEvenProduct : Tendsto
      (fun j : ℕ ↦
        (orbit.state j).amplitude *
          (DFP.TwoLeg.observableMap
            ((orbit.state j).ε, p (orbit.state j).ε,
              h (orbit.state j).ε)).initialGradientNorm)
      atTop (𝓝 Glim) := by
    simpa only [mul_one] using hAmplitudeTendsto.mul hInitialNormalized
  have hOddProduct : Tendsto
      (fun j : ℕ ↦
        (orbit.state j).amplitude *
          (DFP.TwoLeg.observableMap
            ((orbit.state j).ε, p (orbit.state j).ε,
              h (orbit.state j).ε)).intermediateGradientNorm)
      atTop (𝓝 Glim) := by
    simpa only [mul_one] using hAmplitudeTendsto.mul hIntermediateNormalized
  have hEven : Tendsto
      (fun j : ℕ ↦ ‖orbit.endpointGradient (2 * j)‖) atTop (𝓝 Glim) := by
    have hpoint (j : ℕ) :
        (orbit.state j).amplitude *
            (DFP.TwoLeg.observableMap
              ((orbit.state j).ε, p (orbit.state j).ε,
                h (orbit.state j).ε)).initialGradientNorm =
          ‖orbit.endpointGradient (2 * j)‖ := by
      rw [endpointGradient_even]
      rw [gradientNorm_eq_amplitude_mul_initialObservable
        (orbit.state j) (hvalid j)]
      rw [hgraphCoordinates j]
    exact hEvenProduct.congr' (Eventually.of_forall hpoint)
  have hOdd : Tendsto
      (fun j : ℕ ↦ ‖orbit.endpointGradient (2 * j + 1)‖) atTop (𝓝 Glim) := by
    have hpoint (j : ℕ) :
        (orbit.state j).amplitude *
            (DFP.TwoLeg.observableMap
              ((orbit.state j).ε, p (orbit.state j).ε,
                h (orbit.state j).ε)).intermediateGradientNorm =
          ‖orbit.endpointGradient (2 * j + 1)‖ := by
      rw [endpointGradient_odd]
      rw [middleGradientNorm_eq_amplitude_mul_intermediateObservable
        (orbit.state j) (hvalid j)]
      rw [hgraphCoordinates j]
    exact hOddProduct.congr' (Eventually.of_forall hpoint)
  exact ⟨Glim, hGlim, tendsto_of_tendsto_even_odd hEven hOdd⟩

/-- One common positive interval contains every endpoint-gradient norm on all
sufficiently small canonical slow-curve orbits. -/
theorem slowCurveEndpointGradientNormUniformBounds (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ gmin > 0, ∃ gmax, gmin ≤ gmax ∧
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ k : ℕ, ‖orbit.endpointGradient k‖ ∈ Set.Icc gmin gmax  := by
  obtain ⟨εbarAmplitude, hεbarAmplitude, Gmin, hGmin, Gmax,
      hGminMax, hAmplitude⟩ :=
    slowCurveAmplitudeUniformBounds p h h_invariant h_pJet h_hJet
  obtain ⟨εbarGraph, hεbarGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨εbarValid, hεbarValid, hValid⟩ :=
    ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet εbarGraph hεbarGraph
  have hNormEventually :=
    slowGradientNorms_eventually_mem_Icc p h h_pJet h_hJet
  obtain ⟨r, hr, hrule⟩ := Metric.eventually_nhds_iff.mp hNormEventually
  let εbar := min εbarAmplitude (min εbarValid (r / 2))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hεbarAmplitude.1 (lt_min hεbarValid.1 (half_pos hr))
  have hεbarLt : εbar < 1 / 4 := by
    exact (min_le_left _ _).trans_lt hεbarAmplitude.2
  have hGmaxPos : 0 < Gmax := hGmin.trans_le hGminMax
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, Gmin * (1 / 2),
    mul_pos hGmin (by norm_num), Gmax * (3 / 2), ?_, ?_⟩
  · nlinarith
  · intro ε₀ hε₀
    dsimp only
    let orbit := ofSlowCurve p h ε₀
    change ∀ k : ℕ, ‖orbit.endpointGradient k‖ ∈
      Set.Icc (Gmin * (1 / 2)) (Gmax * (3 / 2))
    have hεbarLeAmplitude : εbar ≤ εbarAmplitude := by
      dsimp only [εbar]
      exact min_le_left _ _
    have hεbarLeValid : εbar ≤ εbarValid := by
      dsimp only [εbar]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hεbarLeRHalf : εbar ≤ r / 2 := by
      dsimp only [εbar]
      exact (min_le_right _ _).trans (min_le_right _ _)
    have hεbarLeGraph : εbar ≤ εbarGraph :=
      hεbarLeValid.trans hεbarValid.2
    have hε₀Amplitude : ε₀ ∈ Set.Ioc 0 εbarAmplitude :=
      ⟨hε₀.1, hε₀.2.trans hεbarLeAmplitude⟩
    have hε₀Valid : ε₀ ∈ Set.Ioc 0 εbarValid :=
      ⟨hε₀.1, hε₀.2.trans hεbarLeValid⟩
    have hε₀Graph : ε₀ ∈ Set.Ioc 0 εbarGraph :=
      ⟨hε₀.1, hε₀.2.trans hεbarLeGraph⟩
    obtain ⟨Glim, hGlimBounds, hGlimTendsto, hAmplitudeBoundsRaw⟩ :=
      hAmplitude ε₀ hε₀Amplitude
    have hAmplitudeBounds (j : ℕ) :
        (orbit.state j).amplitude ∈ Set.Icc Gmin Gmax := by
      simpa only [orbit] using hAmplitudeBoundsRaw j
    have hvalid (j : ℕ) : State.PhaseValidity (orbit.state j) := by
      simpa only [orbit] using hValid ε₀ hε₀Valid j
    have hεcoord (j : ℕ) :
        (orbit.state j).ε = (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
      have hcoordinates := ofSlowCurve_coordinates p h ε₀ j
      have hcoordinates' : (orbit.state j).coordinates =
          DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
        simpa only [orbit] using hcoordinates
      simpa only [State.coordinates_def] using congrArg Prod.fst hcoordinates'
    have hgraphCoordinates (j : ℕ) :
        (orbit.state j).coordinates =
          ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
      obtain ⟨hcoordinateGraph, _⟩ := hGraph ε₀ hε₀Graph j
      calc
        (orbit.state j).coordinates = DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
          simpa only [orbit] using ofSlowCurve_coordinates p h ε₀ j
        _ = ((DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
            p (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
            h (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) := hcoordinateGraph
        _ = ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
          rw [hεcoord j]
    have hscaleState (j : ℕ) : (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
      obtain ⟨_, hscale⟩ := hGraph ε₀ hε₀Graph j
      rw [hεcoord j]
      exact hscale
    have hnormalized (j : ℕ) :
        (DFP.TwoLeg.observableMap ((orbit.state j).ε, p (orbit.state j).ε,
            h (orbit.state j).ε)).initialGradientNorm ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
          (DFP.TwoLeg.observableMap ((orbit.state j).ε, p (orbit.state j).ε,
            h (orbit.state j).ε)).intermediateGradientNorm ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) := by
      have hs := hscaleState j
      have hdist : dist (orbit.state j).ε 0 < r := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
        exact (hs.2.trans (hε₀.2.trans hεbarLeRHalf)).trans_lt (half_lt_self hr)
      exact hrule hdist
    apply endpointGradientNorm_mem_Icc_of_amplitude_and_normalized
      orbit Gmin Gmax (1 / 2) (3 / 2) hGmin.le (by norm_num) hvalid
      hAmplitudeBounds
    intro j
    rw [hgraphCoordinates j]
    exact hnormalized j

end DFP.TwoPhaseOrbit
