module

import ReasLib.LinearAlgebra.Matrix.OrthogonalTransport
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientLimit.Basic
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradient
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeBounds
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.GradientNormSlowGraph
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables.GradientNormSmoothness
import Mathlib.LinearAlgebra.UnitaryGroup

public section

noncomputable section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit

/-- A valid boundary gradient factors into its positive amplitude and initial observable norm. -/
theorem gradientNorm_eq_amplitude_mul_initialObservable
    (s : State) (hs : State.PhaseValidity s) :
    ‖s.gradient‖ =
      s.amplitude * (DFP.TwoLeg.observableMap s.coordinates).initialGradientNorm := by
  have hnorms := congrArg Prod.fst
    (DFP.TwoLeg.observableMap_gradientNorms s.ε s.p s.h)
  simp only [] at hnorms
  rw [State.gradient_def, norm_smul, Real.norm_eq_abs, abs_of_pos hs.amplitude_pos]
  rw [Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
    s.frame hs.frame_specialOrthogonal]
  rw [State.coordinates_def, hnorms]

/-- A valid intermediate gradient factors into its positive amplitude and
intermediate observable norm. -/
theorem middleGradientNorm_eq_amplitude_mul_intermediateObservable
    (s : State) (hs : State.PhaseValidity s) :
    ‖s.middleGradient‖ =
      s.amplitude *
        (DFP.TwoLeg.observableMap s.coordinates).intermediateGradientNorm := by
  have hnorms := congrArg (fun norms ↦ norms.2.1)
    (DFP.TwoLeg.observableMap_gradientNorms s.ε s.p s.h)
  simp only [] at hnorms
  rw [State.middleGradient_def, norm_smul, Real.norm_eq_abs,
    abs_of_pos hs.amplitude_pos]
  rw [Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
    s.frame hs.frame_specialOrthogonal]
  rw [State.coordinates_def, hnorms]

/-- Both normalized endpoint norms enter a fixed positive interval along a slow graph. -/
theorem slowGradientNorms_eventually_mem_Icc
    (p h : ℝ → ℝ)
    (h_pJet : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∀ᶠ ε in 𝓝 (0 : ℝ),
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm ∈
          Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm ∈
          Set.Icc (1 / 2 : ℝ) (3 / 2) := by
  let graph := DFP.TwoLeg.SlowGraph.ofAsymptotics p h h_pJet h_hJet
  simpa only [graph, DFP.TwoLeg.SlowGraph.path_apply,
    DFP.TwoLeg.SlowGraph.ofAsymptotics_shape,
    DFP.TwoLeg.SlowGraph.ofAsymptotics_high] using
    graph.eventually_gradientNorms_mem_Icc
      (a := (1 / 2 : ℝ)) (b := 3 / 2) (by norm_num) (by norm_num)

/-- Amplitude and normalized-observable intervals give a uniform endpoint-gradient interval,
with the even and odd endpoint branches transported separately. -/
theorem endpointGradientNorm_mem_Icc_of_amplitude_and_normalized
    (orbit : DFP.TwoPhaseOrbit) (A B a b : ℝ)
    (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hvalid : ∀ j, State.PhaseValidity (orbit.state j))
    (hAmplitude : ∀ j, (orbit.state j).amplitude ∈ Set.Icc A B)
    (hNormalized : ∀ j,
      (DFP.TwoLeg.observableMap (orbit.state j).coordinates).initialGradientNorm ∈
          Set.Icc a b ∧
        (DFP.TwoLeg.observableMap (orbit.state j).coordinates).intermediateGradientNorm ∈
          Set.Icc a b) :
    ∀ k, ‖orbit.endpointGradient k‖ ∈ Set.Icc (A * a) (B * b) := by
  have hB : 0 ≤ B := by
    have hzero := hAmplitude 0
    exact hA.trans (hzero.1.trans hzero.2)
  have hb : 0 ≤ b := by
    have hzero := (hNormalized 0).1
    exact ha.trans (hzero.1.trans hzero.2)
  intro k
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [endpointGradient_even]
    rw [gradientNorm_eq_amplitude_mul_initialObservable (orbit.state j) (hvalid j)]
    have hAmplitudeAt := hAmplitude j
    have hNormalizedAt := (hNormalized j).1
    constructor
    · calc
        A * a ≤ (orbit.state j).amplitude * a :=
          mul_le_mul_of_nonneg_right hAmplitudeAt.1 ha
        _ ≤ (orbit.state j).amplitude *
            (DFP.TwoLeg.observableMap (orbit.state j).coordinates).initialGradientNorm :=
          mul_le_mul_of_nonneg_left hNormalizedAt.1 (hvalid j).amplitude_pos.le
    · calc
        (orbit.state j).amplitude *
            (DFP.TwoLeg.observableMap (orbit.state j).coordinates).initialGradientNorm ≤
            (orbit.state j).amplitude * b :=
          mul_le_mul_of_nonneg_left hNormalizedAt.2 (hvalid j).amplitude_pos.le
        _ ≤ B * b := mul_le_mul_of_nonneg_right hAmplitudeAt.2 hb
  · rw [endpointGradient_odd]
    rw [middleGradientNorm_eq_amplitude_mul_intermediateObservable
      (orbit.state j) (hvalid j)]
    have hAmplitudeAt := hAmplitude j
    have hNormalizedAt := (hNormalized j).2
    constructor
    · calc
        A * a ≤ (orbit.state j).amplitude * a :=
          mul_le_mul_of_nonneg_right hAmplitudeAt.1 ha
        _ ≤ (orbit.state j).amplitude *
            (DFP.TwoLeg.observableMap (orbit.state j).coordinates).intermediateGradientNorm :=
          mul_le_mul_of_nonneg_left hNormalizedAt.1 (hvalid j).amplitude_pos.le
    · calc
        (orbit.state j).amplitude *
            (DFP.TwoLeg.observableMap (orbit.state j).coordinates).intermediateGradientNorm ≤
            (orbit.state j).amplitude * b :=
          mul_le_mul_of_nonneg_left hNormalizedAt.2 (hvalid j).amplitude_pos.le
        _ ≤ B * b := mul_le_mul_of_nonneg_right hAmplitudeAt.2 hb

end DFP.TwoPhaseOrbit
