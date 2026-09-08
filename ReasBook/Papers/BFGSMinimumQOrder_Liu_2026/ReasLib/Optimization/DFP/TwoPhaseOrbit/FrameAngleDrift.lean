module

public import ReasLib.Analysis.Asymptotics.UniformRemainder.BigOToExplicit
public import ReasLib.Optimization.DFP.TwoPhaseControls.FrameAngleJet.Specialization
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.OrbitBounds
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.FrameAngle

public section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

/-- Along sufficiently small invariant slow-curve orbits, the unwrapped physical
frame angle advances by `-3 * ε ^ 2` with a uniform fourth-order remainder. -/
theorem slowCurveFrameRotation (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Cφ > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar, ∀ j : ℕ,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        let εj := (orbit.state j).ε
        |orbit.frameAngle (j + 1) - orbit.frameAngle j + 3 * εj ^ 2| ≤
          Cφ * εj ^ 4 := by
  have hExpansion :=
    DFP.TwoLeg.frameAngleExpansionOfGraphJets p h h_pJet h_hJet
  have hFourSeven : (4 : ℕ) < 7 := by
    norm_num
  have hSevenFour :
      (fun ε : ℝ ↦ ε ^ 7) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    (Asymptotics.isLittleO_pow_pow hFourSeven).isBigO
  have hExpansionFour :
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).frameAngleIncrement -
          (-3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 4) :=
    hExpansion.trans hSevenFour
  have hFourFive : (4 : ℕ) < 5 := by
    norm_num
  have hFiveFour :
      (fun ε : ℝ ↦ ε ^ 5) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    (Asymptotics.isLittleO_pow_pow hFourFive).isBigO
  have hFourSix : (4 : ℕ) < 6 := by
    norm_num
  have hSixFour :
      (fun ε : ℝ ↦ ε ^ 6) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    (Asymptotics.isLittleO_pow_pow hFourSix).isBigO
  have hFifthCorrection :
      (fun ε : ℝ ↦ (-196 / 5 : ℝ) * ε ^ 5) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 4) :=
    hFiveFour.const_mul_left (-196 / 5 : ℝ)
  have hSixthCorrection :
      (fun ε : ℝ ↦ (28 / 5 : ℝ) * ε ^ 6) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 4) :=
    hSixFour.const_mul_left (28 / 5 : ℝ)
  have hCorrection :
      (fun ε : ℝ ↦ (-196 / 5 : ℝ) * ε ^ 5 + (28 / 5 : ℝ) * ε ^ 6) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 4) :=
    hFifthCorrection.add hSixthCorrection
  have hCombined := hExpansionFour.add hCorrection
  have hCombinedIdentity (ε : ℝ) :
      ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).frameAngleIncrement -
          (-3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6)) +
          ((-196 / 5 : ℝ) * ε ^ 5 + (28 / 5 : ℝ) * ε ^ 6) =
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).frameAngleIncrement +
          3 * ε ^ 2 := by
    ring
  have hFourthOrder :
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).frameAngleIncrement +
          3 * ε ^ 2) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    hCombined.congr_left hCombinedIdentity
  obtain ⟨Cφ, hCφ, δ, hδ, hlocal⟩ :=
    Asymptotics.IsUniformRemainderOn.exists_pos_natPow_bound_of_isBigO hFourthOrder
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min ηGraph (δ / 2)
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηGraph.1 (half_pos hδ)
  have hεbarLt : εbar < 1 / 4 := by
    exact lt_of_le_of_lt (min_le_left _ _) hηGraph.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, Cφ, hCφ, ?_⟩
  intro ε₀ hε₀ j
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  let xj := DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)
  have hεbarGraph : εbar ≤ ηGraph := min_le_left _ _
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans hεbarGraph⟩
  have hxj := hGraph ε₀ hε₀Graph j
  have hεjPos : 0 < xj.1 := hxj.2.1
  have hεbarDeltaHalf : εbar ≤ δ / 2 := min_le_right _ _
  have hδHalfLt : δ / 2 < δ := half_lt_self hδ
  have hεjDelta : |xj.1| < δ := by
    rw [abs_of_pos hεjPos]
    exact hxj.2.2.trans_lt
      (hε₀.2.trans_lt (hεbarDeltaHalf.trans_lt hδHalfLt))
  have hlocalBound := hlocal xj.1 hεjDelta
  have hlocalBound' :
      |(DFP.TwoLeg.observableMap (xj.1, p xj.1, h xj.1)).frameAngleIncrement +
          3 * xj.1 ^ 2| ≤ Cφ * xj.1 ^ 4 := by
    simpa only [Real.norm_eq_abs, abs_of_pos hεjPos] using hlocalBound
  have hcoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
  have hcoordinates' : (orbit.state j).coordinates = xj := by
    simpa only [orbit, xj] using hcoordinates
  have hεj : (orbit.state j).ε = xj.1 := by
    rw [State.coordinates_def] at hcoordinates'
    exact congrArg Prod.fst hcoordinates'
  have hgraphCoordinates : xj = (xj.1, p xj.1, h xj.1) := hxj.1
  have horbitCoordinates :
      (orbit.state j).coordinates = (xj.1, p xj.1, h xj.1) :=
    hcoordinates'.trans hgraphCoordinates
  rw [frameAngleIncrement_eq_observable, horbitCoordinates, hεj]
  exact hlocalBound'

end DFP.TwoPhaseOrbit
