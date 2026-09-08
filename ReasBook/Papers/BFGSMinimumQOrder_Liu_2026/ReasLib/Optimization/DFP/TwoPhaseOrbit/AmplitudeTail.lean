module

public import ReasLib.Analysis.Asymptotics.PositiveProduct
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.PowerTail
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleSummability
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeDrift
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeLimit
public import ReasLib.Optimization.DFP.TwoPhaseOrbit

public section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit

/-- The amplitude excess of a sufficiently small invariant slow-curve orbit is
asymptotic to `(13 / 3) * Glim * ε` at every positive limiting amplitude `Glim`. -/
theorem slowCurveAmplitudeTailEquivalent (p h : ℝ → ℝ)
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
      ∀ Glim > 0,
        Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
      (fun j : ℕ ↦ (orbit.state j).amplitude - Glim) ~[atTop]
            (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε) := by
  obtain ⟨εbarValid, hεbarValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet
      (1 / 8) (by norm_num)
  obtain ⟨εbarSum, hεbarSum, hSum⟩ :=
    DFP.TwoLeg.slowCurveScaleFourthPowerSummable p h h_invariant h_pJet h_hJet
  obtain ⟨εbarTail, hεbarTail, hTail⟩ :=
    DFP.TwoLeg.slowCurveFourthPowerTailIsEquivalent p h h_invariant h_pJet h_hJet
  obtain ⟨εbarScale, hεbarScale, hScale⟩ :=
    DFP.TwoLeg.slowCurveScaleAsymptotic p h h_invariant h_pJet h_hJet
  obtain ⟨εbarGraph, hεbarGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min (min (min εbarValid εbarSum) εbarTail)
    (min εbarScale εbarGraph)
  have hεbar_pos : 0 < εbar := by
    dsimp [εbar]
    exact lt_min (lt_min (lt_min hεbarValid.1 hεbarSum) hεbarTail)
      (lt_min hεbarScale hεbarGraph.1)
  refine ⟨εbar, hεbar_pos, ?_⟩
  intro ε₀ hε₀
  dsimp
  intro Glim hGlim hGlim_tendsto
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεbar_le_valid : εbar ≤ εbarValid := by
    dsimp [εbar]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεbar_le_sum : εbar ≤ εbarSum := by
    dsimp [εbar]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεbar_le_tail : εbar ≤ εbarTail := by
    dsimp [εbar]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hεbar_le_scale : εbar ≤ εbarScale := by
    dsimp [εbar]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεbar_le_graph : εbar ≤ εbarGraph := by
    dsimp [εbar]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hε₀Valid : ε₀ ∈ Set.Ioc 0 εbarValid :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_valid⟩
  have hε₀Sum : ε₀ ∈ Set.Ioc 0 εbarSum :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_sum⟩
  have hε₀Tail : ε₀ ∈ Set.Ioc 0 εbarTail :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_tail⟩
  have hε₀Scale : ε₀ ∈ Set.Ioc 0 εbarScale :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_scale⟩
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 εbarGraph :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_graph⟩
  have hvalid (j : ℕ) : State.PhaseValidity (orbit.state j) := by
    exact hValid ε₀ hε₀Valid j
  have hεcoord (j : ℕ) :
      (orbit.state j).ε = (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    exact congrArg Prod.fst (by simpa [orbit, State.coordinates_def] using hcoord)
  have hεzero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) := by
    have hbase : Tendsto (fun j : ℕ ↦ (9 / 2 : ℝ) * (j : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
    have hpow : Tendsto
        (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) atTop (𝓝 0) := by
      convert (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 : ℝ) / 3)).comp hbase using 1
      · funext j
        dsimp [Function.comp_def]
        congr 1
        ring
    have hscale := hScale ε₀ hε₀Scale
    have hstate : Tendsto
        (fun j : ℕ ↦ (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1)
        atTop (𝓝 0) := hscale.symm.tendsto_nhds hpow
    exact hstate.congr' (Eventually.of_forall (fun j ↦ (hεcoord j).symm))
  let u : ℕ → ℝ := fun j ↦ (orbit.state j).ε ^ 4
  let a : ℕ → ℝ := fun j ↦ (orbit.state j).amplitude
  have hu_nonneg : ∀ j, 0 ≤ u j := by
    intro j
    simpa [u] using pow_nonneg (le_of_lt (hvalid j).ε_pos) 4
  have hu : Summable u := by
    have hs := hSum ε₀ hε₀Sum
    simpa [u, hεcoord] using hs
  have ha_pos : ∀ j, 0 < a j := by
    intro j
    exact (hvalid j).amplitude_pos
  have hratio :
      (fun j ↦ a (j + 1) / a j - (1 - (13 / 2 : ℝ) * u j)) =o[atTop] u := by
    have hlittle := DFP.TwoLeg.slowCurveAmplitudeDriftLittleO p h h_pJet h_hJet
    have hcomp := hlittle.comp_tendsto hεzero
    have hpoint (j : ℕ) :
        a (j + 1) / a j - (1 - (13 / 2 : ℝ) * u j) =
          (DFP.TwoLeg.observableMap
              ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε)).amplitudeRatio -
            (1 - (13 / 2 : ℝ) * (orbit.state j).ε ^ 4) := by
      obtain ⟨hcoordGraph, _⟩ := hGraph ε₀ hε₀Graph j
      have hcoord : (orbit.state j).coordinates =
          ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
        calc
          (orbit.state j).coordinates =
              DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
                simpa [orbit] using DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
          _ = ((DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
            p (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
            h (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) := hcoordGraph
          _ = ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
            rw [hεcoord j]
      have hsucc : orbit.state (j + 1) = (orbit.state j).next := by
        simpa [orbit] using DFP.TwoPhaseOrbit.ofSlowCurve_succ p h ε₀ j
      have hratio' := State.nextAmplitudeRatio (orbit.state j)
        (ne_of_gt (hvalid j).amplitude_pos)
      dsimp [a, u]
      rw [hsucc, hratio', hcoord]
    exact hcomp.congr' (Eventually.of_forall (fun j ↦ (hpoint j).symm))
      (Eventually.of_forall (fun j ↦ rfl))
  have htail :
      (fun j ↦ ∑' k : ℕ, u (j + k)) ~[atTop]
        (fun j ↦ (2 / 3 : ℝ) * (orbit.state j).ε) := by
    have htail' := hTail ε₀ hε₀Tail
    dsimp at htail'
    refine (htail'.congr_left ?_).congr_right ?_
    · filter_upwards [] with j
      dsimp [u]
      apply tsum_congr
      intro k
      rw [hεcoord (j + k)]
    · filter_upwards [] with j
      rw [hεcoord j]
  have hmain := PositiveProduct.subLimitIsEquivalent hu_nonneg hu ha_pos hratio
    hGlim_tendsto htail (by norm_num : (13 / 2 : ℝ) ≠ 0)
  have hcoeff (j : ℕ) :
      (13 / 2 : ℝ) * Glim * ((2 / 3 : ℝ) * (orbit.state j).ε) =
        (13 / 3 : ℝ) * Glim * (orbit.state j).ε := by
    ring
  simpa [a, orbit] using hmain.congr_right (Eventually.of_forall hcoeff)

/-- Every sufficiently small invariant slow-curve orbit has a positive limiting
amplitude whose excess has first-order coefficient `13 / 3` in the scale. -/
theorem slowCurveAmplitudeAsymptotics (p h : ℝ → ℝ)
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
        Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) ∧
            (fun j : ℕ ↦ (orbit.state j).amplitude - Glim) ~[atTop]
            (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε) := by
  obtain ⟨εbarLimit, hεbarLimit, hLimit⟩ :=
    slowCurveAmplitudeExistsPositiveLimit p h h_invariant h_pJet h_hJet
  obtain ⟨εbarTail, hεbarTail, hTail⟩ :=
    slowCurveAmplitudeTailEquivalent p h h_invariant h_pJet h_hJet
  let εbar := min εbarLimit εbarTail
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hεbarLimit hεbarTail
  refine ⟨εbar, hεbarPos, ?_⟩
  intro ε₀ hε₀
  dsimp only
  have hεbar_le_limit : εbar ≤ εbarLimit := by
    dsimp only [εbar]
    exact min_le_left _ _
  have hεbar_le_tail : εbar ≤ εbarTail := by
    dsimp only [εbar]
    exact min_le_right _ _
  have hε₀Limit : ε₀ ∈ Set.Ioc 0 εbarLimit :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_limit⟩
  have hε₀Tail : ε₀ ∈ Set.Ioc 0 εbarTail :=
    ⟨hε₀.1, hε₀.2.trans hεbar_le_tail⟩
  obtain ⟨Glim, hGlim, hGlimTendsto⟩ := hLimit ε₀ hε₀Limit
  have hTail' := hTail ε₀ hε₀Tail Glim hGlim hGlimTendsto
  exact ⟨Glim, hGlim, hGlimTendsto, hTail'⟩

end DFP.TwoPhaseOrbit
