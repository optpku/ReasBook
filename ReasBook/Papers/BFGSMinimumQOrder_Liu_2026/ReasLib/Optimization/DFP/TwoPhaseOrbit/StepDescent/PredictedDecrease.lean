module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepDescent.StepNorm
import ReasLib.Analysis.Normed.QuadraticBounds
import ReasLib.Optimization.DFP.AbstractSecantStep.PhaseBounds
import ReasLib.Optimization.DFP.TwoPhaseOrbit.ExactCycle.Transport

public section

noncomputable section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit

/-- Uniformly over both phases and every sufficiently small slow-curve orbit,
the predicted decrease is bounded above and below by positive multiples of the
squared endpoint radius. -/
private theorem phasePredictedDecreaseUniformBoundsOfData (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cQ > 0, ∃ CQ > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ j : ℕ, ∀ i : Fin 2,
          let k := 2 * j + i.val
          let s := orbit.endpoint (k + 1) - orbit.endpoint k
          let q := -inner ℝ (orbit.endpointGradient k) s
          let r := orbit.endpointRadius k
          q ∈ Set.Icc (cQ * r ^ 2) (CQ * r ^ 2) := by
  obtain ⟨ηStep, hηStep, cStep, hcStep, CStep, hCStep, hStep⟩ :=
    slowCurvePhaseStepNormUniformBounds p h h_invariant h_pJet h_hJet
  obtain ⟨εbar, hεbar, hExact⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurveExact p h h_invariant h_pJet h_hJet ηStep hηStep
  let cQ : ℝ := (3 / 4) * cStep ^ 2
  let CQ : ℝ := (9 / 2) * CStep ^ 2
  have hcQ : 0 < cQ := mul_pos (by norm_num) (sq_pos_of_pos hcStep)
  have hCQ : 0 < CQ := mul_pos (by norm_num) (sq_pos_of_pos hCStep)
  have hεbarIoo : εbar ∈ Set.Ioo (0 : ℝ) (1 / 4) :=
    ⟨hεbar.1, hεbar.2.trans_lt hηStep.2⟩
  refine ⟨εbar, hεbarIoo, cQ, hcQ, CQ, hCQ, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεStep : ε₀ ∈ Set.Ioc 0 ηStep :=
    ⟨hε₀.1, hε₀.2.trans hεbar.2⟩
  intro j i
  have hexact := hExact ε₀ hε₀ j
  have hstep := hStep ε₀ hεStep j i
  have hr : 0 ≤ orbit.endpointRadius (2 * j + i.val) := by
    rw [endpointRadius_def]
    exact sq_nonneg _
  have habstract := (hexact.step i).predictedDecrease_mem_Icc_of_phase
    (orbit.state j).ε i hexact.valid.ε_pos hexact.valid.ε_lt_quarter
    (hexact.step_secantMatrix_eq_phase i) (hexact.step_tau_eq_phase i)
  have hphysical :
      -inner ℝ (orbit.endpointGradient (2 * j + i.val))
          (orbit.endpoint (2 * j + i.val + 1) -
            orbit.endpoint (2 * j + i.val)) ∈
        Set.Icc
          ((3 / 4 : ℝ) *
            ‖orbit.endpoint (2 * j + i.val + 1) -
              orbit.endpoint (2 * j + i.val)‖ ^ 2)
          ((9 / 2 : ℝ) *
            ‖orbit.endpoint (2 * j + i.val + 1) -
              orbit.endpoint (2 * j + i.val)‖ ^ 2) := by
    rw [endpointPredictedDecrease_eq_exactStep orbit j i hexact,
      endpointStepNorm_eq_exactStep orbit j i hexact]
    exact habstract
  have hcombined := quadraticQuantity_mem_Icc_of_norm_mem_Icc
    hr hcStep.le hCStep.le (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (0 : ℝ) ≤ 9 / 2) hstep hphysical
  simpa only [cQ, CQ] using hcombined

end DFP.TwoPhaseOrbit

namespace DFP.TwoLeg.SlowCurve

/-- Uniformly over both phases of an invariant slow curve, predicted decrease
is bounded above and below by positive multiples of the squared endpoint
radius. -/
theorem phasePredictedDecreaseUniformBounds (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cQ > 0, ∃ CQ > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ j : ℕ, ∀ i : Fin 2,
          let k := 2 * j + i.val
          let s := orbit.endpoint (k + 1) - orbit.endpoint k
          let q := -inner ℝ (orbit.endpointGradient k) s
          let r := orbit.endpointRadius k
          q ∈ Set.Icc (cQ * r ^ 2) (CQ * r ^ 2) := by
  exact DFP.TwoPhaseOrbit.phasePredictedDecreaseUniformBoundsOfData
    curve.shape curve.high curve.isInvariant
      curve.shapeRemainder curve.highRemainder

end DFP.TwoLeg.SlowCurve

namespace DFP.TwoPhaseOrbit

/-- Unbundled compatibility form of
`DFP.TwoLeg.SlowCurve.phasePredictedDecreaseUniformBounds`. -/
theorem slowCurvePhasePredictedDecreaseUniformBounds (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cQ > 0, ∃ CQ > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ j : ℕ, ∀ i : Fin 2,
          let k := 2 * j + i.val
          let s := orbit.endpoint (k + 1) - orbit.endpoint k
          let q := -inner ℝ (orbit.endpointGradient k) s
          let r := orbit.endpointRadius k
          q ∈ Set.Icc (cQ * r ^ 2) (CQ * r ^ 2) := by
  let curve :=
    DFP.TwoLeg.SlowCurve.ofAsymptotics p h h_pJet h_hJet h_invariant
  have hBounds := DFP.TwoLeg.SlowCurve.phasePredictedDecreaseUniformBounds curve
  simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hBounds

end DFP.TwoPhaseOrbit
