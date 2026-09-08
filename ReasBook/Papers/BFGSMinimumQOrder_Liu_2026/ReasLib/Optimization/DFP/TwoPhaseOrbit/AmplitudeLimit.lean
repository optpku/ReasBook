module

public import ReasLib.Analysis.Asymptotics.PositiveProduct
public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet.Specialization
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleSummability
public import ReasLib.Optimization.DFP.TwoPhaseOrbit
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeDrift

public section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit

/-- For every sufficiently small positive initial scale, the amplitude of the canonical
slow-curve orbit converges to a strictly positive limit. -/
theorem slowCurveAmplitudeExistsPositiveLimit (p h : ℝ → ℝ)
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
      let orbit := ofSlowCurve p h ε₀
      ∃ Glim > 0,
        Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) := by
  have honeEighth : (1 / 8 : ℝ) ∈ Set.Ioo 0 (1 / 4) := by
    norm_num
  obtain ⟨εbarValid, hεbarValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet
      (1 / 8) honeEighth
  obtain ⟨εbarSum, hεbarSum, hSum⟩ :=
    DFP.TwoLeg.slowCurveScaleFourthPowerSummable p h h_invariant h_pJet h_hJet
  obtain ⟨εbarGraph, hεbarGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min (min εbarValid εbarSum) εbarGraph
  have hεbar_pos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min (lt_min hεbarValid.1 hεbarSum) hεbarGraph.1
  refine ⟨εbar, hεbar_pos, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεbar_le_valid : εbar ≤ εbarValid := by
    dsimp only [εbar]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hεbar_le_sum : εbar ≤ εbarSum := by
    dsimp only [εbar]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hεbar_le_graph : εbar ≤ εbarGraph := by
    dsimp only [εbar]
    exact min_le_right _ _
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
    have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hcoord' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hcoord
    have hfst := congrArg Prod.fst hcoord'
    simpa only [State.coordinates_def] using hfst
  let u : ℕ → ℝ := fun j ↦ (orbit.state j).ε ^ 4
  let a : ℕ → ℝ := fun j ↦ (orbit.state j).amplitude
  have hu_nonneg : ∀ j, 0 ≤ u j := by
    intro j
    exact pow_nonneg (hvalid j).ε_pos.le 4
  have hu : Summable u := by
    have hs := hSum ε₀ hε₀Sum
    simpa only [u, hεcoord] using hs
  have ha_pos : ∀ j, 0 < a j := by
    intro j
    exact (hvalid j).amplitude_pos
  have hpowZero : Tendsto u atTop (𝓝 0) := hu.tendsto_atTop_zero
  have hεzero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) := by
    have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
    have hfour_ne : 4 ≠ 0 := by norm_num
    have hFourCast : ((4 : ℕ) : ℝ) = 4 := by
      norm_num
    have hroot := hpowZero.rpow_const_nhds_zero hquarter
    have hrootEq (j : ℕ) : u j ^ (1 / 4 : ℝ) = (orbit.state j).ε := by
      have hidentity := Real.pow_rpow_inv_natCast (hvalid j).ε_pos.le hfour_ne
      rw [hFourCast] at hidentity
      dsimp only [u]
      rw [one_div]
      exact hidentity
    exact hroot.congr' (Eventually.of_forall hrootEq)
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
                simpa only [orbit] using
                  DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
          _ = ((DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
            p (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
            h (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) := hcoordGraph
          _ = ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
            rw [hεcoord j]
      have hsucc : orbit.state (j + 1) = (orbit.state j).next := by
        simpa only [orbit] using DFP.TwoPhaseOrbit.ofSlowCurve_succ p h ε₀ j
      have hratio' := State.nextAmplitudeRatio (orbit.state j)
        (ne_of_gt (hvalid j).amplitude_pos)
      dsimp only [a, u]
      rw [hsucc, hratio', hcoord]
    exact hcomp.congr' (Eventually.of_forall (fun j ↦ (hpoint j).symm))
      (Eventually.of_forall (fun _ ↦ rfl))
  obtain ⟨Glim, hGlim, hGlim_tendsto⟩ :=
    PositiveProduct.existsLimit hu_nonneg hu ha_pos hratio
  have hGlim_tendsto' : Tendsto
      (fun j : ℕ ↦ ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j).amplitude)
        atTop (𝓝 Glim) := by
    simpa only [a, orbit] using hGlim_tendsto
  exact ⟨Glim, hGlim, hGlim_tendsto'⟩

end DFP.TwoPhaseOrbit
