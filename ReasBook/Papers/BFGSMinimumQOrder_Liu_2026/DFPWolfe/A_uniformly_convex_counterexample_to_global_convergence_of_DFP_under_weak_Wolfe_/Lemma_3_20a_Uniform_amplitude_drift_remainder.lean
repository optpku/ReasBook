module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeDrift

public section

open Filter
open scoped Topology

/- Along a graph with the prescribed slow-curve jets, the fourth-order
amplitude-ratio remainder is little-o of `ε ^ 4` at zero. -/
#check (DFP.TwoLeg.slowCurveAmplitudeDriftLittleO :
  ∀ (p h : ℝ → ℝ),
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4)) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 4))

/- Lemma 3.20a (Uniform amplitude-drift remainder): the canonical tail-supremum
modulus tends to zero and uniformly controls the fourth-order physical amplitude
drift of every sufficiently small exact slow-curve orbit. -/
#check (DFP.TwoPhaseOrbit.slowCurveAmplitudeDriftModulus :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
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
              (1 - (13 / 2) * εj ^ 4)| ≤ ωA η * εj ^ 4)
