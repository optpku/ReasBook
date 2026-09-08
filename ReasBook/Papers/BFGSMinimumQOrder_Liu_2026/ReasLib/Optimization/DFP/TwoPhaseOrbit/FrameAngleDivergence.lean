module

public import ReasLib.Analysis.Asymptotics.PartialSumDivergence.PowerTwo
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleSummability
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.FrameAngleDrift

public section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

/-- Along every sufficiently small invariant slow-curve orbit, the unwrapped physical
frame angle tends to negative infinity. -/
theorem slowCurveFrameAngleTendstoAtBot (p h : ℝ → ℝ)
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
      Tendsto orbit.frameAngle atTop atBot := by
  obtain ⟨εbarRotation, hεbarRotation, Cφ, hCφ, hrotation⟩ :=
    slowCurveFrameRotation p h h_invariant h_pJet h_hJet
  obtain ⟨εbarScale, hεbarScale, hscale⟩ :=
    DFP.TwoLeg.slowCurveScaleAsymptotic p h h_invariant h_pJet h_hJet
  obtain ⟨εbarDivergence, hεbarDivergence, hdivergence⟩ :=
    DFP.TwoLeg.slowCurveScaleSquareNotSummable p h h_invariant h_pJet h_hJet
  let εbar := min εbarRotation (min εbarScale εbarDivergence)
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hεbarRotation.1 (lt_min hεbarScale hεbarDivergence)
  have hεbarLt : εbar < 1 / 4 := by
    exact lt_of_le_of_lt (min_le_left _ _) hεbarRotation.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Rotation : ε₀ ∈ Set.Ioc 0 εbarRotation := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact min_le_left _ _
  have hε₀Scale : ε₀ ∈ Set.Ioc 0 εbarScale := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hε₀Divergence : ε₀ ∈ Set.Ioc 0 εbarDivergence := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans (min_le_right _ _)
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
  have hforward : ∀ᶠ j : ℕ in atTop,
      |orbit.frameAngle (j + 1) - orbit.frameAngle j +
          3 * (orbit.state j).ε ^ 2| ≤ Cφ * (orbit.state j).ε ^ 4 := by
    apply Eventually.of_forall
    intro j
    simpa only [orbit] using hrotation ε₀ hε₀Rotation j
  have hnotSummable : ¬ Summable (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
    have hiterateNotSummable := hdivergence ε₀ hε₀Divergence
    simpa only [hεcoord] using hiterateNotSummable
  exact tendsto_atBot_of_eventually_abs_forwardDiff_add_le_of_square_vanishing
    hCφ hεzero hforward hnotSummable

end DFP.TwoPhaseOrbit
