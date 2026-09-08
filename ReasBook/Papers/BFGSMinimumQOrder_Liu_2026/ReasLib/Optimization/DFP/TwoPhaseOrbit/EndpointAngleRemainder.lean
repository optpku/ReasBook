module

public import ReasLib.Analysis.Asymptotics.UniformRemainder.ModulusOrderDrop
public import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.Specialization
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.OrbitBounds
public import ReasLib.Optimization.DFP.TwoPhaseOrbit

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

/-- The canonical tail-supremum modulus uniformly controls both real endpoint-gradient
angle remainders along every sufficiently small invariant slow-curve orbit. -/
theorem slowCurveEndpointAngleRemainderModulus (p h : ℝ → ℝ)
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
    let R : Unit → ℝ → ℝ × ℝ := fun _ ε ↦
      ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).firstEndpointAngleIncrement.toReal -
          (-2 * ε ^ 2),
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).secondEndpointAngleIncrement.toReal -
          (-ε ^ 2))
    let ωθ := Asymptotics.uniformRemainderModulus R Set.univ 2
    ∃ η₀ ∈ Set.Ioo 0 (1 / 4),
      Asymptotics.IsUniformRemainderModulusOn R Set.univ 2 η₀ ωθ ∧
        ∀ η ∈ Set.Ioc 0 η₀, ∀ ε₀ ∈ Set.Ioc 0 η, ∀ j : ℕ,
          let state := (DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j
          let observable := DFP.TwoLeg.observableMap state.coordinates
          |observable.firstEndpointAngleIncrement.toReal - (-2 * state.ε ^ 2)| ≤
              ωθ η * state.ε ^ 2 ∧
            |observable.secondEndpointAngleIncrement.toReal - (-state.ε ^ 2)| ≤
              ωθ η * state.ε ^ 2 := by
  let R : Unit → ℝ → ℝ × ℝ := fun _ ε ↦
    ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).firstEndpointAngleIncrement.toReal -
        (-2 * ε ^ 2),
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).secondEndpointAngleIncrement.toReal -
        (-ε ^ 2))
  let ωθ := Asymptotics.uniformRemainderModulus R Set.univ 2
  change ∃ η₀ ∈ Set.Ioo 0 (1 / 4),
    Asymptotics.IsUniformRemainderModulusOn R Set.univ 2 η₀ ωθ ∧
      ∀ η ∈ Set.Ioc 0 η₀, ∀ ε₀ ∈ Set.Ioc 0 η, ∀ j : ℕ,
        let state := (DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j
        let observable := DFP.TwoLeg.observableMap state.coordinates
        |observable.firstEndpointAngleIncrement.toReal - (-2 * state.ε ^ 2)| ≤
            ωθ η * state.ε ^ 2 ∧
          |observable.secondEndpointAngleIncrement.toReal - (-state.ε ^ 2)| ≤
            ωθ η * state.ε ^ 2
  have hFirst :=
    DFP.TwoLeg.EndpointAngleJet.firstLeadingOfGraphJets p h h_pJet h_hJet
  have hSecond :=
    DFP.TwoLeg.EndpointAngleJet.secondLeadingOfGraphJets p h h_pJet h_hJet
  have hPair : (fun ε : ℝ ↦ R () ε) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) := by
    simpa only [R] using hFirst.prod_left hSecond
  obtain ⟨ηModulus, hηModulus, hModulusRaw⟩ :=
    Asymptotics.IsUniformRemainderModulusOn.of_isLittleO_natPow_singleton hPair
  have hTwoCast : ((2 : ℕ) : ℝ) = 2 := by
    norm_num
  rw [hTwoCast] at hModulusRaw
  have hUnitFamily : (fun _ : Unit ↦ fun ε : ℝ ↦ R () ε) = R := by
    funext θ ε
    cases θ
    rfl
  rw [hUnitFamily] at hModulusRaw
  have hModulus :
      Asymptotics.IsUniformRemainderModulusOn R Set.univ 2 ηModulus ωθ := by
    simpa only [ωθ] using hModulusRaw
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let η₀ := min ηModulus ηGraph
  have hη₀Pos : 0 < η₀ := by
    dsimp only [η₀]
    exact lt_min hηModulus hηGraph.1
  have hη₀Lt : η₀ < 1 / 4 := by
    exact lt_of_le_of_lt (min_le_right _ _) hηGraph.2
  have hModulusRestricted :
      Asymptotics.IsUniformRemainderModulusOn R Set.univ 2 η₀ ωθ :=
    Asymptotics.IsUniformRemainderModulusOn.mono_radius hModulus
      (min_le_left _ _)
  refine ⟨η₀, ⟨hη₀Pos, hη₀Lt⟩, hModulusRestricted, ?_⟩
  intro η hη ε₀ hε₀ j
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  let xj := DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)
  have hηGraphLe : η₀ ≤ ηGraph := min_le_right _ _
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans (hη.2.trans hηGraphLe)⟩
  have hxj := hGraph ε₀ hε₀Graph j
  have hxjPos : 0 < xj.1 := hxj.2.1
  have hxjLe : xj.1 ≤ η := hxj.2.2.trans hε₀.2
  have hxjAbsPos : 0 < |xj.1| := by
    rw [abs_of_pos hxjPos]
    exact hxjPos
  have hxjAbsLe : |xj.1| ≤ η := by
    rw [abs_of_pos hxjPos]
    exact hxjLe
  have hPairBound :=
    Asymptotics.IsUniformRemainderModulusOn.bound hModulusRestricted
      (θ := ()) (η := η) (ε := xj.1) (Set.mem_univ ()) hη hxjAbsPos hxjAbsLe
  have hFirstBound : |(R () xj.1).1| ≤ ωθ η * xj.1 ^ 2 := by
    have hcomponent := (norm_fst_le (R () xj.1)).trans hPairBound
    rw [abs_of_pos hxjPos] at hcomponent
    have hPower : xj.1 ^ (2 : ℝ) = xj.1 ^ (2 : ℕ) := by
      rw [← hTwoCast]
      exact Real.rpow_natCast xj.1 2
    rw [hPower] at hcomponent
    simpa only [Real.norm_eq_abs] using hcomponent
  have hSecondBound : |(R () xj.1).2| ≤ ωθ η * xj.1 ^ 2 := by
    have hcomponent := (norm_snd_le (R () xj.1)).trans hPairBound
    rw [abs_of_pos hxjPos] at hcomponent
    have hPower : xj.1 ^ (2 : ℝ) = xj.1 ^ (2 : ℕ) := by
      rw [← hTwoCast]
      exact Real.rpow_natCast xj.1 2
    rw [hPower] at hcomponent
    simpa only [Real.norm_eq_abs] using hcomponent
  have hcoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
  have hcoordinates' : (orbit.state j).coordinates = xj := by
    simpa only [orbit, xj] using hcoordinates
  have hstateScale : (orbit.state j).ε = xj.1 := by
    rw [State.coordinates_def] at hcoordinates'
    exact congrArg Prod.fst hcoordinates'
  have hgraphCoordinates : xj = (xj.1, p xj.1, h xj.1) := hxj.1
  have hstateCoordinates :
      (orbit.state j).coordinates = (xj.1, p xj.1, h xj.1) :=
    hcoordinates'.trans hgraphCoordinates
  rw [hstateCoordinates, hstateScale]
  exact ⟨hFirstBound, hSecondBound⟩

end DFP.TwoPhaseOrbit
