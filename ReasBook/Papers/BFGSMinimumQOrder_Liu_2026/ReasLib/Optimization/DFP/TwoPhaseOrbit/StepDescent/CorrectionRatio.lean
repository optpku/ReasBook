module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepDescent.PredictedDecrease
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointCorrection
public import ReasLib.Analysis.InnerProductSpace.QuotientBounds

public section

noncomputable section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit

/-- Uniformly over both phases, the endpoint-correction contribution relative
to predicted decrease is bounded by a positive constant times the current
cycle scale whenever the boundary centers converge. -/
private theorem phaseCorrectionRatioUniformBoundOfData (p h : ℝ → ℝ)
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
                Kcorr * (orbit.state j).ε := by
  obtain ⟨ηStep, hηStep, cStep, hcStep, CStep, hCStep, hStep⟩ :=
    slowCurvePhaseStepNormUniformBounds p h h_invariant h_pJet h_hJet
  obtain ⟨ηQ, hηQ, cQ, hcQ, CQ, hCQ, hQ⟩ :=
    slowCurvePhasePredictedDecreaseUniformBounds p h h_invariant h_pJet h_hJet
  obtain ⟨ηCorrection, hηCorrection, Kcorrection, hKcorrection, hCorrection⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointCorrectionUniformBound
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηValid, hηValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity
      p h h_invariant h_pJet h_hJet (1 / 8) (by constructor <;> norm_num)
  let εbar := min ηStep (min ηQ (min ηCorrection ηValid))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηStep.1 (lt_min hηQ.1 (lt_min hηCorrection.1 hηValid.1))
  have hεbarLt : εbar < 1 / 4 :=
    (min_le_left _ _).trans_lt hηStep.2
  let Kcorr := Kcorrection * CStep / cQ
  have hKcorr : 0 < Kcorr :=
    div_pos (mul_pos hKcorrection hCStep) hcQ
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, Kcorr, hKcorr, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεStep : ε₀ ∈ Set.Ioc 0 ηStep :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεQ : ε₀ ∈ Set.Ioc 0 ηQ := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεCorrection : ε₀ ∈ Set.Ioc 0 ηCorrection := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hεValid : ε₀ ∈ Set.Ioc 0 ηValid := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  intro Clim hClim j i
  let k := 2 * j + i.val
  let s := orbit.endpoint (k + 1) - orbit.endpoint k
  let q := -inner ℝ (orbit.endpointGradient k) s
  let r := orbit.endpointRadius k
  let εj := (orbit.state j).ε
  have hkdiv : k / 2 = j := by
    dsimp only [k]
    fin_cases i <;> omega
  have hεjPos : 0 < εj := by
    simpa only [orbit, εj] using (hValid ε₀ hεValid j).ε_pos
  have hr : r = εj ^ 2 := by
    dsimp only [r, εj]
    rw [endpointRadius_def, hkdiv]
  have hcorrectionBound :
      ‖orbit.endpointCorrection Clim k‖ ≤ Kcorrection * εj ^ 3 := by
    have hc := hCorrection ε₀ hεCorrection Clim hClim k
    simpa only [orbit, εj, hkdiv] using hc
  have hstepBound : ‖s‖ ≤ CStep * r := by
    have hs := (hStep ε₀ hεStep j i).2
    simpa only [orbit, k, s, r] using hs
  have hqBound : cQ * r ^ 2 ≤ q := by
    have hq := (hQ ε₀ hεQ j i).1
    simpa only [orbit, k, s, q, r] using hq
  have hratio := abs_inner_div_le_scale
    (orbit.endpointCorrection Clim k) s εj r q Kcorrection CStep cQ
    hεjPos hKcorrection hCStep hcQ hr hcorrectionBound hstepBound hqBound
  simpa only [Kcorr, orbit, k, s, q, εj] using hratio

end DFP.TwoPhaseOrbit

namespace DFP.TwoLeg.SlowCurve

/-- Uniformly over both phases of an invariant slow curve, the endpoint
correction relative to predicted decrease is at most linear in the cycle
scale whenever the boundary centers converge. -/
theorem phaseCorrectionRatioUniformBound (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kcorr > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ j : ℕ, ∀ i : Fin 2,
              let k := 2 * j + i.val
              let s := orbit.endpoint (k + 1) - orbit.endpoint k
              let q := -inner ℝ (orbit.endpointGradient k) s
              |inner ℝ (orbit.endpointCorrection Clim k) s / q| ≤
                Kcorr * (orbit.state j).ε := by
  exact DFP.TwoPhaseOrbit.phaseCorrectionRatioUniformBoundOfData
    curve.shape curve.high curve.isInvariant
      curve.shapeRemainder curve.highRemainder

end DFP.TwoLeg.SlowCurve

namespace DFP.TwoPhaseOrbit

/-- Unbundled compatibility form of
`DFP.TwoLeg.SlowCurve.phaseCorrectionRatioUniformBound`. -/
theorem slowCurvePhaseCorrectionRatioUniformBound (p h : ℝ → ℝ)
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
                Kcorr * (orbit.state j).ε := by
  let curve :=
    DFP.TwoLeg.SlowCurve.ofAsymptotics p h h_pJet h_hJet h_invariant
  have hBound := DFP.TwoLeg.SlowCurve.phaseCorrectionRatioUniformBound curve
  simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hBound

end DFP.TwoPhaseOrbit
