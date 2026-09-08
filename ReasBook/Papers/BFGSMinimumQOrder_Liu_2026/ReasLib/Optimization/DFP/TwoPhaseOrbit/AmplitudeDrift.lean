module

public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet.Specialization
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.OrbitBounds
public import ReasLib.Optimization.DFP.TwoPhaseOrbit

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

namespace State

/-- The ratio of the next physical amplitude to a nonzero current amplitude is the
normalized amplitude observable of the current two-leg coordinates. -/
theorem nextAmplitudeRatio (s : State) (h_amplitude : s.amplitude ≠ 0) :
    s.next.amplitude / s.amplitude =
      (DFP.TwoLeg.observableMap s.coordinates).amplitudeRatio := by
  rw [State.next_amplitude, DFP.TwoLeg.observableMap_amplitudeRatio,
    State.coordinates_def]
  field_simp

end State

/-- The canonical tail-supremum modulus uniformly controls the fourth-order
physical amplitude drift along every sufficiently small invariant slow-curve orbit. -/
theorem slowCurveAmplitudeDriftModulus (p h : ℝ → ℝ)
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
    let R : Unit → ℝ → ℝ := fun _ ε ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4)
    let ωA := Asymptotics.uniformRemainderModulus R Set.univ 4
    ∃ η₀ ∈ Set.Ioo 0 (1 / 4),
      Asymptotics.IsUniformRemainderModulusOn R Set.univ 4 η₀ ωA ∧
        ∀ η ∈ Set.Ioc 0 η₀, ∀ ε₀ ∈ Set.Ioc 0 η, ∀ j : ℕ,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
          let state := orbit.state j
          let εj := state.ε
          |(orbit.state (j + 1)).amplitude / state.amplitude -
              (1 - (13 / 2) * εj ^ 4)| ≤ ωA η * εj ^ 4 := by
  let R : Unit → ℝ → ℝ := fun _ ε ↦
    (DFP.TwoLeg.observableMap (ε, p ε, h ε)).amplitudeRatio -
      (1 - (13 / 2) * ε ^ 4)
  let ωA := Asymptotics.uniformRemainderModulus R Set.univ 4
  change ∃ η₀ ∈ Set.Ioo 0 (1 / 4),
    Asymptotics.IsUniformRemainderModulusOn R Set.univ 4 η₀ ωA ∧
      ∀ η ∈ Set.Ioc 0 η₀, ∀ ε₀ ∈ Set.Ioc 0 η, ∀ j : ℕ,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        let state := orbit.state j
        let εj := state.ε
        |(orbit.state (j + 1)).amplitude / state.amplitude -
            (1 - (13 / 2) * εj ^ 4)| ≤ ωA η * εj ^ 4
  have hLittle : (fun ε : ℝ ↦ R () ε) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) := by
    simpa [R] using DFP.TwoLeg.slowCurveAmplitudeDriftLittleO p h h_pJet h_hJet
  obtain ⟨ηMod, hηMod, hMod⟩ :=
    Asymptotics.IsUniformRemainderModulusOn.of_isLittleO_natPow_singleton hLittle
  have hModR : Asymptotics.IsUniformRemainderModulusOn R Set.univ 4 ηMod ωA := by
    simpa [R, ωA] using hMod
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηValid, hηValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet
      ηGraph hηGraph
  let η₀ := min ηMod ηValid
  have hη₀_pos : 0 < η₀ := lt_min hηMod hηValid.1
  have hη₀_lt : η₀ < 1 / 4 :=
    lt_of_le_of_lt (min_le_right ηMod ηValid) (lt_of_le_of_lt hηValid.2 hηGraph.2)
  refine ⟨η₀, ⟨hη₀_pos, hη₀_lt⟩, ?_, ?_⟩
  · exact Asymptotics.IsUniformRemainderModulusOn.mono_radius hModR
      (min_le_left ηMod ηValid)
  · intro η hη ε₀ hε₀ j
    let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
    let state := orbit.state j
    let εj := state.ε
    change |(orbit.state (j + 1)).amplitude / state.amplitude -
      (1 - (13 / 2) * εj ^ 4)| ≤ ωA η * εj ^ 4
    have hη_to_graph : η ≤ ηGraph :=
      hη.2.trans ((min_le_right ηMod ηValid).trans hηValid.2)
    have hη_to_mod : η ≤ ηMod := hη.2.trans (min_le_left ηMod ηValid)
    have hε₀Graph : ε₀ ∈ Set.Ioc 0 ηGraph :=
      ⟨hε₀.1, hε₀.2.trans hη_to_graph⟩
    have hε₀Valid : ε₀ ∈ Set.Ioc 0 ηValid :=
      ⟨hε₀.1, hε₀.2.trans (hη.2.trans (min_le_right ηMod ηValid))⟩
    have hηModMem : η ∈ Set.Ioc 0 ηMod := ⟨hη.1, hη_to_mod⟩
    obtain ⟨hcoordGraph, hscale⟩ := hGraph ε₀ hε₀Graph j
    have hvalid := hValid ε₀ hε₀Valid j
    have hεj_pos : 0 < εj := by
      have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
      have hε : εj = (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 :=
        congrArg Prod.fst (by simpa [State.coordinates_def] using hcoord)
      rw [hε]
      exact hscale.1
    have hεj_le : εj ≤ η := by
      have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
      have hε : εj = (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 :=
        congrArg Prod.fst (by simpa [State.coordinates_def] using hcoord)
      rw [hε]
      exact hscale.2.trans hε₀.2
    have hcoord : state.coordinates = (εj, p εj, h εj) := by
      have hstate := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
      have hε : εj = (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 :=
        congrArg Prod.fst (by simpa [State.coordinates_def] using hstate)
      calc
        state.coordinates = DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := hstate
        _ = ((DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          p (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          h (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) := hcoordGraph
        _ = (εj, p εj, h εj) := by rw [← hε]
    have hratio := State.nextAmplitudeRatio state (ne_of_gt hvalid.amplitude_pos)
    have hsucc : orbit.state (j + 1) = state.next :=
      DFP.TwoPhaseOrbit.ofSlowCurve_succ p h ε₀ j
    have hbound := Asymptotics.IsUniformRemainderModulusOn.bound hModR
      (θ := ()) (η := η) (ε := εj) (Set.mem_univ ()) hηModMem
      (abs_pos.mpr (ne_of_gt hεj_pos))
      (by simpa [abs_of_pos hεj_pos] using hεj_le)
    have hbound' : |R () εj| ≤ ωA η * εj ^ 4 := by
      simpa [R, Real.norm_eq_abs, abs_of_pos hεj_pos, ωA] using hbound
    calc
      |(orbit.state (j + 1)).amplitude / state.amplitude -
          (1 - (13 / 2) * εj ^ 4)|
          = |state.next.amplitude / state.amplitude -
            (1 - (13 / 2) * εj ^ 4)| := by rw [hsucc]
      _ = |(DFP.TwoLeg.observableMap (εj, p εj, h εj)).amplitudeRatio -
          (1 - (13 / 2) * εj ^ 4)| := by rw [hratio, hcoord]
      _ = |R () εj| := by rfl
      _ ≤ ωA η * εj ^ 4 := hbound'

end DFP.TwoPhaseOrbit
