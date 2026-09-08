module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleAsymptotics
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.FrameAngleDrift

public section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

/-- For a sufficiently small invariant slow-curve orbit, adjacent unwrapped frame
angles are eventually strictly decreasing. -/
theorem slowCurveFrameAngleEventuallyStrictlyDecreases (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ᶠ j : ℕ in atTop, orbit.frameAngle (j + 1) < orbit.frameAngle j := by
  obtain ⟨εbarRotation, hεbarRotation, Cφ, hCφ, hrotation⟩ :=
    slowCurveFrameRotation p h h_invariant h_pJet h_hJet
  obtain ⟨εbarScale, hεbarScale, hscale⟩ :=
    DFP.TwoLeg.slowCurveScaleAsymptotic p h h_invariant h_pJet h_hJet
  obtain ⟨εbarGraph, hεbarGraph, hgraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min εbarRotation (min εbarScale εbarGraph)
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hεbarRotation.1 (lt_min hεbarScale hεbarGraph.1)
  have hεbarLt : εbar < 1 / 4 := by
    exact (min_le_left _ _).trans_lt hεbarRotation.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Rotation : ε₀ ∈ Set.Ioc 0 εbarRotation := by
    exact ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hε₀Scale : ε₀ ∈ Set.Ioc 0 εbarScale := by
    exact ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 εbarGraph := by
    exact ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hεcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hcoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hcoordinates' :
        (orbit.state j).coordinates =
          DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hcoordinates
    rw [State.coordinates_def] at hcoordinates'
    exact congrArg Prod.fst hcoordinates'
  have hεzero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) := by
    have hNineHalfPos : (0 : ℝ) < 9 / 2 := by
      norm_num
    have hbase : Tendsto (fun j : ℕ ↦ (9 / 2 : ℝ) * (j : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hNineHalfPos
    have hOneThirdPos : (0 : ℝ) < 1 / 3 := by
      norm_num
    have hpow : Tendsto
        (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3))
        atTop (𝓝 0) := by
      convert (tendsto_rpow_neg_atTop hOneThirdPos).comp hbase using 1
      · funext j
        dsimp only [Function.comp_apply]
        congr 1
        ring
    have hscaleOrbit := hscale ε₀ hε₀Scale
    have hiterateZero : Tendsto
        (fun j : ℕ ↦
          (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1)
        atTop (𝓝 0) :=
      hscaleOrbit.symm.tendsto_nhds hpow
    exact hiterateZero.congr' (Eventually.of_forall (fun j ↦ (hεcoord j).symm))
  have hεpos (j : ℕ) : 0 < (orbit.state j).ε := by
    have horbit := hgraph ε₀ hε₀Graph j
    rw [hεcoord j]
    exact horbit.2.1
  have hrotationOrbit (j : ℕ) :
      |orbit.frameAngle (j + 1) - orbit.frameAngle j +
          3 * (orbit.state j).ε ^ 2| ≤ Cφ * (orbit.state j).ε ^ 4 := by
    simpa only [orbit] using hrotation ε₀ hε₀Rotation j
  have hscaledSquareZero : Tendsto
      (fun j : ℕ ↦ Cφ * (orbit.state j).ε ^ 2) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ Cφ) atTop (𝓝 Cφ) :=
      tendsto_const_nhds
    convert hconst.mul (hεzero.pow 2) using 1
    norm_num
  have hthreePos : (0 : ℝ) < 3 := by
    norm_num
  have hsmall : ∀ᶠ j : ℕ in atTop, Cφ * (orbit.state j).ε ^ 2 < 3 :=
    hscaledSquareZero.eventually (Iio_mem_nhds hthreePos)
  filter_upwards [hsmall] with j hj
  have hupper := (abs_le.mp (hrotationOrbit j)).2
  have hεsquarePos : 0 < (orbit.state j).ε ^ 2 := pow_pos (hεpos j) 2
  have hquarticLt : Cφ * (orbit.state j).ε ^ 4 <
      3 * (orbit.state j).ε ^ 2 := by
    calc
      Cφ * (orbit.state j).ε ^ 4 =
          (Cφ * (orbit.state j).ε ^ 2) * (orbit.state j).ε ^ 2 := by
        ring
      _ < 3 * (orbit.state j).ε ^ 2 :=
        mul_lt_mul_of_pos_right hj hεsquarePos
  linarith

/-- For a sufficiently small invariant slow-curve orbit, the adjacent unwrapped
frame-angle decreases converge to zero. -/
theorem slowCurveFrameAngleDecreaseTendstoZero (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      Tendsto (fun j : ℕ ↦ orbit.frameAngle j - orbit.frameAngle (j + 1))
        atTop (𝓝 0) := by
  obtain ⟨εbarRotation, hεbarRotation, Cφ, hCφ, hrotation⟩ :=
    slowCurveFrameRotation p h h_invariant h_pJet h_hJet
  obtain ⟨εbarScale, hεbarScale, hscale⟩ :=
    DFP.TwoLeg.slowCurveScaleAsymptotic p h h_invariant h_pJet h_hJet
  let εbar := min εbarRotation εbarScale
  have hεbarPos : 0 < εbar := by
    exact lt_min hεbarRotation.1 hεbarScale
  have hεbarLt : εbar < 1 / 4 := by
    exact (min_le_left _ _).trans_lt hεbarRotation.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Rotation : ε₀ ∈ Set.Ioc 0 εbarRotation := by
    exact ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hε₀Scale : ε₀ ∈ Set.Ioc 0 εbarScale := by
    exact ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  have hεcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hcoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hcoordinates' :
        (orbit.state j).coordinates =
          DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hcoordinates
    rw [State.coordinates_def] at hcoordinates'
    exact congrArg Prod.fst hcoordinates'
  have hεzero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) := by
    have hNineHalfPos : (0 : ℝ) < 9 / 2 := by
      norm_num
    have hbase : Tendsto (fun j : ℕ ↦ (9 / 2 : ℝ) * (j : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hNineHalfPos
    have hOneThirdPos : (0 : ℝ) < 1 / 3 := by
      norm_num
    have hpow : Tendsto
        (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3))
        atTop (𝓝 0) := by
      convert (tendsto_rpow_neg_atTop hOneThirdPos).comp hbase using 1
      · funext j
        dsimp only [Function.comp_apply]
        congr 1
        ring
    have hscaleOrbit := hscale ε₀ hε₀Scale
    have hiterateZero : Tendsto
        (fun j : ℕ ↦
          (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1)
        atTop (𝓝 0) :=
      hscaleOrbit.symm.tendsto_nhds hpow
    exact hiterateZero.congr' (Eventually.of_forall (fun j ↦ (hεcoord j).symm))
  have hrotationOrbit (j : ℕ) :
      |orbit.frameAngle (j + 1) - orbit.frameAngle j +
          3 * (orbit.state j).ε ^ 2| ≤ Cφ * (orbit.state j).ε ^ 4 := by
    simpa only [orbit] using hrotation ε₀ hε₀Rotation j
  have hfourthOrderZero : Tendsto
      (fun j : ℕ ↦ Cφ * (orbit.state j).ε ^ 4) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ Cφ) atTop (𝓝 Cφ) :=
      tendsto_const_nhds
    convert hconst.mul (hεzero.pow 4) using 1
    norm_num
  have hremainderZero : Tendsto
      (fun j : ℕ ↦ orbit.frameAngle (j + 1) - orbit.frameAngle j +
        3 * (orbit.state j).ε ^ 2) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun j ↦ norm_nonneg _) ?_ hfourthOrderZero
    intro j
    simpa only [Real.norm_eq_abs] using hrotationOrbit j
  have hsquareZero : Tendsto
      (fun j : ℕ ↦ 3 * (orbit.state j).ε ^ 2) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ (3 : ℝ)) atTop (𝓝 3) :=
      tendsto_const_nhds
    convert hconst.mul (hεzero.pow 2) using 1
    norm_num
  have hdeltaRaw : Tendsto
      (fun j : ℕ ↦
        (orbit.frameAngle (j + 1) - orbit.frameAngle j +
          3 * (orbit.state j).ε ^ 2) - 3 * (orbit.state j).ε ^ 2)
      atTop (𝓝 0) := by
    convert hremainderZero.sub hsquareZero using 1
    norm_num
  have hdeltaIdentity (j : ℕ) :
      (orbit.frameAngle (j + 1) - orbit.frameAngle j +
          3 * (orbit.state j).ε ^ 2) - 3 * (orbit.state j).ε ^ 2 =
        orbit.frameAngle (j + 1) - orbit.frameAngle j := by
    ring
  have hdelta : Tendsto
      (fun j : ℕ ↦ orbit.frameAngle (j + 1) - orbit.frameAngle j)
      atTop (𝓝 0) := by
    exact hdeltaRaw.congr' (Eventually.of_forall hdeltaIdentity)
  have hdecreaseIdentity (j : ℕ) :
      -(orbit.frameAngle (j + 1) - orbit.frameAngle j) =
        orbit.frameAngle j - orbit.frameAngle (j + 1) := by
    ring
  have hnegative : Tendsto
      (fun j : ℕ ↦ -(orbit.frameAngle (j + 1) - orbit.frameAngle j))
      atTop (𝓝 0) := by
    convert hdelta.neg using 1
    norm_num
  exact hnegative.congr' (Eventually.of_forall hdecreaseIdentity)

end DFP.TwoPhaseOrbit
