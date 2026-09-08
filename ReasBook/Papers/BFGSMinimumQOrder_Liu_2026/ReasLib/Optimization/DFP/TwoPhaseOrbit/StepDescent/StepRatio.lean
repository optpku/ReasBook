module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepDescent.PredictedDecrease
import ReasLib.Analysis.Normed.QuadraticBounds
import ReasLib.Optimization.DFP.AbstractSecantStep.PhaseBounds
import ReasLib.Optimization.DFP.TwoPhaseOrbit.ExactCycle.Transport

public section

noncomputable section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit

/-- Uniformly over both phases, the squared-step-to-decrease ratio differs from
the prescribed phase ratio by at most a positive constant times the current
cycle scale. -/
private theorem phaseStepRatioUniformBoundOfData (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kratio > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ j : ℕ, ∀ i : Fin 2,
          let k := 2 * j + i.val
          let s := orbit.endpoint (k + 1) - orbit.endpoint k
          let q := -inner ℝ (orbit.endpointGradient k) s
          |‖s‖ ^ 2 / q - (TwoPhaseControls.phase (orbit.state j).ε i).tau| ≤
            Kratio * (orbit.state j).ε := by
  obtain ⟨ηStep, hηStep, cStep, hcStep, CStep, hCStep, hStep⟩ :=
    slowCurvePhaseStepNormUniformBounds p h h_invariant h_pJet h_hJet
  obtain ⟨ηQ, hηQ, cQ, hcQ, CQ, hCQ, hQ⟩ :=
    slowCurvePhasePredictedDecreaseUniformBounds p h
      h_invariant h_pJet h_hJet
  let η := min ηStep ηQ
  have hη : η ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    dsimp only [η]
    exact ⟨lt_min hηStep.1 hηQ.1,
      (min_le_left _ _).trans_lt hηStep.2⟩
  obtain ⟨εbar, hεbar, hExact⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurveExact p h h_invariant h_pJet h_hJet η hη
  let Kratio : ℝ := 2 * CStep ^ 2 / cQ
  have hKratio : 0 < Kratio :=
    div_pos (mul_pos (by norm_num) (sq_pos_of_pos hCStep)) hcQ
  have hεbarIoo : εbar ∈ Set.Ioo (0 : ℝ) (1 / 4) :=
    ⟨hεbar.1, hεbar.2.trans_lt hη.2⟩
  refine ⟨εbar, hεbarIoo, Kratio, hKratio, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεStep : ε₀ ∈ Set.Ioc 0 ηStep :=
    ⟨hε₀.1, hε₀.2.trans (hεbar.2.trans (min_le_left _ _))⟩
  have hεQ : ε₀ ∈ Set.Ioc 0 ηQ :=
    ⟨hε₀.1, hε₀.2.trans (hεbar.2.trans (min_le_right _ _))⟩
  intro j i
  have hexact := hExact ε₀ hε₀ j
  have hstep := hStep ε₀ hεStep j i
  have hq := hQ ε₀ hεQ j i
  have habstract := (hexact.step i).phaseStepRatio_deviation_le
    (orbit.state j).ε i (hexact.step_secantMatrix_eq_phase i)
      (hexact.step_tau_eq_phase i)
  have hdeviation :
      |‖orbit.endpoint (2 * j + i.val + 1) -
            orbit.endpoint (2 * j + i.val)‖ ^ 2 /
          (-inner ℝ (orbit.endpointGradient (2 * j + i.val))
            (orbit.endpoint (2 * j + i.val + 1) -
              orbit.endpoint (2 * j + i.val))) -
          (TwoPhaseControls.phase (orbit.state j).ε i).tau| ≤
        2 * |(orbit.state j).ε| *
            ‖orbit.endpoint (2 * j + i.val + 1) -
              orbit.endpoint (2 * j + i.val)‖ ^ 2 /
          (-inner ℝ (orbit.endpointGradient (2 * j + i.val))
            (orbit.endpoint (2 * j + i.val + 1) -
              orbit.endpoint (2 * j + i.val))) := by
    rw [endpointPredictedDecrease_eq_exactStep orbit j i hexact,
      endpointStepNorm_eq_exactStep orbit j i hexact]
    exact habstract
  have hkdiv : (2 * j + i.val) / 2 = j := by omega
  have hradius :
      orbit.endpointRadius (2 * j + i.val) = (orbit.state j).ε ^ 2 := by
    rw [endpointRadius_def, hkdiv]
  have hradiusPos : 0 < orbit.endpointRadius (2 * j + i.val) := by
    rw [hradius]
    exact sq_pos_of_pos hexact.valid.ε_pos
  have hratio := squaredNorm_div_mem_Icc_of_norm_mem_Icc
    hradiusPos hcStep.le hCStep.le hcQ hCQ hstep hq
  calc
    |‖orbit.endpoint (2 * j + i.val + 1) -
          orbit.endpoint (2 * j + i.val)‖ ^ 2 /
        (-inner ℝ (orbit.endpointGradient (2 * j + i.val))
          (orbit.endpoint (2 * j + i.val + 1) -
            orbit.endpoint (2 * j + i.val))) -
        (TwoPhaseControls.phase (orbit.state j).ε i).tau| ≤
      2 * |(orbit.state j).ε| *
          ‖orbit.endpoint (2 * j + i.val + 1) -
            orbit.endpoint (2 * j + i.val)‖ ^ 2 /
        (-inner ℝ (orbit.endpointGradient (2 * j + i.val))
          (orbit.endpoint (2 * j + i.val + 1) -
            orbit.endpoint (2 * j + i.val))) := hdeviation
    _ = 2 * (orbit.state j).ε *
        (‖orbit.endpoint (2 * j + i.val + 1) -
            orbit.endpoint (2 * j + i.val)‖ ^ 2 /
          (-inner ℝ (orbit.endpointGradient (2 * j + i.val))
            (orbit.endpoint (2 * j + i.val + 1) -
              orbit.endpoint (2 * j + i.val)))) := by
      rw [abs_of_pos hexact.valid.ε_pos]
      ring
    _ ≤ 2 * (orbit.state j).ε * (CStep ^ 2 / cQ) :=
      mul_le_mul_of_nonneg_left hratio.2
        (mul_nonneg (by norm_num) hexact.valid.ε_pos.le)
    _ = Kratio * (orbit.state j).ε := by
      dsimp only [Kratio]
      ring

end DFP.TwoPhaseOrbit

namespace DFP.TwoLeg.SlowCurve

/-- Uniformly over both phases of an invariant slow curve, the
squared-step-to-decrease ratio differs from the prescribed phase ratio by at
most a positive constant times the cycle scale. -/
theorem phaseStepRatioUniformBound (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kratio > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ j : ℕ, ∀ i : Fin 2,
          let k := 2 * j + i.val
          let s := orbit.endpoint (k + 1) - orbit.endpoint k
          let q := -inner ℝ (orbit.endpointGradient k) s
          |‖s‖ ^ 2 / q - (TwoPhaseControls.phase (orbit.state j).ε i).tau| ≤
            Kratio * (orbit.state j).ε := by
  exact DFP.TwoPhaseOrbit.phaseStepRatioUniformBoundOfData
    curve.shape curve.high curve.isInvariant
      curve.shapeRemainder curve.highRemainder

end DFP.TwoLeg.SlowCurve

namespace DFP.TwoPhaseOrbit

/-- Unbundled compatibility form of
`DFP.TwoLeg.SlowCurve.phaseStepRatioUniformBound`. -/
theorem slowCurvePhaseStepRatioUniformBound (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kratio > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ j : ℕ, ∀ i : Fin 2,
          let k := 2 * j + i.val
          let s := orbit.endpoint (k + 1) - orbit.endpoint k
          let q := -inner ℝ (orbit.endpointGradient k) s
          |‖s‖ ^ 2 / q - (TwoPhaseControls.phase (orbit.state j).ε i).tau| ≤
            Kratio * (orbit.state j).ε := by
  let curve :=
    DFP.TwoLeg.SlowCurve.ofAsymptotics p h h_pJet h_hJet h_invariant
  have hBound := DFP.TwoLeg.SlowCurve.phaseStepRatioUniformBound curve
  simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hBound

end DFP.TwoPhaseOrbit
