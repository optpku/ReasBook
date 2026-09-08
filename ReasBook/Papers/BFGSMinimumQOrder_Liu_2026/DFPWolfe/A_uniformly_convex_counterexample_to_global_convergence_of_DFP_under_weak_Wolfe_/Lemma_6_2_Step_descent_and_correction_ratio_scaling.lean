module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepDescent

public section

open Filter
open scoped Asymptotics Topology

/- Lemma 6.2 (Step, descent, and correction-ratio scaling) (1): uniformly over
both phases and every sufficiently small slow-curve orbit, the physical step norm
is bounded above and below by positive multiples of the endpoint radius. -/
#check (DFP.TwoPhaseOrbit.slowCurvePhaseStepNormUniformBounds :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cStep > 0, ∃ CStep > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ j : ℕ, ∀ i : Fin 2,
          let k := 2 * j + i.val
          let s := orbit.endpoint (k + 1) - orbit.endpoint k
          let r := orbit.endpointRadius k
          ‖s‖ ∈ Set.Icc (cStep * r) (CStep * r))

/- Lemma 6.2 (Step, descent, and correction-ratio scaling) (2): uniformly over
both phases and every sufficiently small slow-curve orbit, predicted decrease is
bounded above and below by positive multiples of the squared endpoint radius. -/
#check (DFP.TwoPhaseOrbit.slowCurvePhasePredictedDecreaseUniformBounds :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cQ > 0, ∃ CQ > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ j : ℕ, ∀ i : Fin 2,
          let k := 2 * j + i.val
          let s := orbit.endpoint (k + 1) - orbit.endpoint k
          let q := -inner ℝ (orbit.endpointGradient k) s
          let r := orbit.endpointRadius k
          q ∈ Set.Icc (cQ * r ^ 2) (CQ * r ^ 2))

/- Lemma 6.2 (Step, descent, and correction-ratio scaling) (3): uniformly over
both phases, the endpoint-correction contribution relative to predicted decrease
is bounded by a positive constant times the current cycle scale. -/
#check (DFP.TwoPhaseOrbit.slowCurvePhaseCorrectionRatioUniformBound :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kcorr > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ j : ℕ, ∀ i : Fin 2,
              let k := 2 * j + i.val
              let s := orbit.endpoint (k + 1) - orbit.endpoint k
              let q := -inner ℝ (orbit.endpointGradient k) s
              |inner ℝ (orbit.endpointCorrection Clim k) s / q| ≤
                Kcorr * (orbit.state j).ε)

/- Lemma 6.2 (Step, descent, and correction-ratio scaling) (4): uniformly over
both phases, the squared-step-to-decrease ratio differs from the prescribed phase
ratio by at most a positive constant times the current cycle scale. -/
#check (DFP.TwoPhaseOrbit.slowCurvePhaseStepRatioUniformBound :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kratio > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ j : ℕ, ∀ i : Fin 2,
          let k := 2 * j + i.val
          let s := orbit.endpoint (k + 1) - orbit.endpoint k
          let q := -inner ℝ (orbit.endpointGradient k) s
          |‖s‖ ^ 2 / q - (TwoPhaseControls.phase (orbit.state j).ε i).tau| ≤
            Kratio * (orbit.state j).ε)
