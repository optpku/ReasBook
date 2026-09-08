module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeTail
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.PhaseRadiusApproximation
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Distance
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointCorrection
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.InvariantGraph
import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeTailUniform
import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeBounds
import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepDescent.StepNorm
import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.OrbitBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

public section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit

/-- Interleaving two sequences that are each asymptotic to a common sequence
preserves that asymptotic relation after flattening by the index quotient. -/
private theorem interleaveIsEquivalent
    (f f0 f1 g : ℕ → ℝ)
    (heven : ∀ j, f (2 * j) = f0 j)
    (hodd : ∀ j, f (2 * j + 1) = f1 j)
    (h0 : f0 ~[atTop] g) (h1 : f1 ~[atTop] g) :
    f ~[atTop] (fun k ↦ g (k / 2)) := by
  change (fun k ↦ f k - g (k / 2)) =o[atTop] (fun k ↦ g (k / 2))
  have h0' : (fun j ↦ f0 j - g j) =o[atTop] g := h0.isLittleO
  have h1' : (fun j ↦ f1 j - g j) =o[atTop] g := h1.isLittleO
  have htwoNe : (2 : ℕ) ≠ 0 := by
    norm_num
  have hdiv : Tendsto (fun k : ℕ ↦ k / 2) atTop atTop :=
    Nat.tendsto_div_const_atTop htwoNe
  apply Asymptotics.IsLittleO.of_isBigOWith
  intro c hc
  have h0c := (h0'.comp_tendsto hdiv).forall_isBigOWith hc
  have h1c := (h1'.comp_tendsto hdiv).forall_isBigOWith hc
  apply Asymptotics.IsBigOWith.of_bound
  filter_upwards [h0c.bound, h1c.bound] with k hk0 hk1
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hq : (2 * j) / 2 = j := by omega
    rw [heven, hq]
    simpa only [Function.comp_apply, hq] using hk0
  · have hq : (2 * j + 1) / 2 = j := by omega
    rw [hodd, hq]
    simpa only [Function.comp_apply, hq] using hk1

/-- The distance of every sufficiently small invariant slow-curve endpoint to
its limiting circle is asymptotic to the first-order amplitude excess. -/
theorem slowCurveEndpointLimitCircleDistanceEquivalent (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              (fun k : ℕ ↦ Metric.infDist (orbit.endpoint k)
                (DFP.TwoPhaseOrbit.limitCircle Clim Glim)) ~[atTop]
                (fun k : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state (k / 2)).ε) := by
  obtain ⟨ηAmp, hηAmp, hAmp⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeTailEquivalent
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηPhase, hηPhase, hPhase⟩ :=
    DFP.TwoPhaseOrbit.slowCurvePhaseRadiusErrorIsLittleO p h h_invariant h_pJet h_hJet
  have honeEighth : (1 / 8 : ℝ) ∈ Set.Ioo 0 (1 / 4) := by
    norm_num
  obtain ⟨ηValid, hηValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet
      (1 / 8) honeEighth
  let εbar := min (min ηAmp ηPhase) ηValid
  have hεbarPos : 0 < εbar := by
    exact lt_min (lt_min hηAmp hηPhase.1) hηValid.1
  have hεbarLt : εbar < 1 / 4 := by
    exact ((min_le_left _ _).trans (min_le_right _ _)).trans_lt hηPhase.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεAmp : ε₀ ∈ Set.Ioc 0 ηAmp :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hεPhase : ε₀ ∈ Set.Ioc 0 ηPhase :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hεValid : ε₀ ∈ Set.Ioc 0 ηValid :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  have hvalid (j : ℕ) : DFP.TwoPhaseOrbit.State.PhaseValidity (orbit.state j) := by
    simpa only [orbit] using hValid ε₀ hεValid j
  intro Clim hClim Glim hGlim hGlimTendsto
  have hAmpEq :
      (fun j : ℕ ↦ (orbit.state j).amplitude - Glim) ~[atTop]
        (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε) := by
    simpa only [orbit] using hAmp ε₀ hεAmp Glim hGlim hGlimTendsto
  have hAmpDiffZero :
      Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude - Glim) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ Glim) atTop (𝓝 Glim) := tendsto_const_nhds
    simpa only [orbit, sub_self] using hGlimTendsto.sub hconst
  have hTargetZero :
      Tendsto (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε)
        atTop (𝓝 0) := hAmpEq.tendsto_nhds hAmpDiffZero
  have hthirteenThirdsNe : (13 / 3 : ℝ) ≠ 0 := by
    norm_num
  have hcoeff : (13 / 3 : ℝ) * Glim ≠ 0 :=
    mul_ne_zero hthirteenThirdsNe (ne_of_gt hGlim)
  have hScaleZero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) := by
    have hscaled := hTargetZero.const_mul (((13 / 3 : ℝ) * Glim)⁻¹)
    simpa only [← mul_assoc, inv_mul_cancel₀ hcoeff, one_mul, mul_zero] using hscaled
  have hSquareLittleScale :
      (fun j : ℕ ↦ (orbit.state j).ε ^ 2) =o[atTop]
        (fun j : ℕ ↦ (orbit.state j).ε) := by
    have honeLtTwo : (1 : ℕ) < 2 := by
      norm_num
    have hbase :=
      (Asymptotics.isLittleO_pow_pow honeLtTwo).comp_tendsto hScaleZero
    simpa only [Function.comp_def, pow_one] using hbase
  have hPhaseLittle (σ : Fin 2) :
      (fun j : ℕ ↦
          ‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
            (orbit.state j).amplitude) =o[atTop]
        (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
    simpa only [orbit] using hPhase ε₀ hεPhase Clim hClim σ
  have hSigned (σ : Fin 2) :
      (fun j : ℕ ↦ ‖orbit.endpoint (2 * j + σ.val) - Clim‖ - Glim) ~[atTop]
        (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε) := by
    have herror :
        (fun j : ℕ ↦
            ‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
              (orbit.state j).amplitude) =o[atTop]
          (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε) :=
      ((hPhaseLittle σ).trans hSquareLittleScale).const_mul_right hcoeff
    refine (hAmpEq.add_isLittleO herror).congr_left ?_
    filter_upwards [] with j
    let r : ℝ := ‖orbit.endpoint (2 * j + σ.val) - Clim‖
    change ((orbit.state j).amplitude - Glim) +
      (r - (orbit.state j).amplitude) = r - Glim
    ring
  have hDistancePhase (σ : Fin 2) :
      (fun j : ℕ ↦ Metric.infDist (orbit.endpoint (2 * j + σ.val))
          (DFP.TwoPhaseOrbit.limitCircle Clim Glim)) ~[atTop]
        (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε) := by
    have hthirteenThirdsPos : (0 : ℝ) < 13 / 3 := by
      norm_num
    have htargetPos : ∀ j : ℕ,
        0 < (13 / 3 : ℝ) * Glim * (orbit.state j).ε := by
      intro j
      exact mul_pos (mul_pos hthirteenThirdsPos hGlim) (hvalid j).ε_pos
    have hsignedPos := (hSigned σ).eventually_pos (Eventually.of_forall htargetPos)
    refine (hSigned σ).congr_left ?_
    filter_upwards [hsignedPos] with j hj
    symm
    rw [DFP.TwoPhaseOrbit.infDist_limitCircle Clim Glim hGlim]
    exact abs_of_pos hj
  have hEven := hDistancePhase (0 : Fin 2)
  have hOdd := hDistancePhase (1 : Fin 2)
  have hEven' : (fun j : ℕ ↦ Metric.infDist (orbit.endpoint (2 * j))
      (DFP.TwoPhaseOrbit.limitCircle Clim Glim)) ~[atTop]
      (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε) := by
    simpa using hEven
  have hOdd' : (fun j : ℕ ↦ Metric.infDist (orbit.endpoint (2 * j + 1))
      (DFP.TwoPhaseOrbit.limitCircle Clim Glim)) ~[atTop]
      (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε) := by
    simpa using hOdd
  have hFlatten := interleaveIsEquivalent
    (fun k : ℕ ↦ Metric.infDist (orbit.endpoint k)
      (DFP.TwoPhaseOrbit.limitCircle Clim Glim))
    (fun j : ℕ ↦ Metric.infDist (orbit.endpoint (2 * j))
      (DFP.TwoPhaseOrbit.limitCircle Clim Glim))
    (fun j : ℕ ↦ Metric.infDist (orbit.endpoint (2 * j + 1))
      (DFP.TwoPhaseOrbit.limitCircle Clim Glim))
    (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε)
    (fun _ ↦ rfl) (fun _ ↦ rfl)
    hEven' hOdd'
  simpa only using hFlatten

/-- The squared cycle scale is little-o of the endpoint distance to the
limiting circle for every sufficiently small invariant slow-curve orbit. -/
theorem slowCurveEndpointRadiusIsLittleODistance (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              (fun k : ℕ ↦ (orbit.state (k / 2)).ε ^ 2) =o[atTop]
                (fun k : ℕ ↦ Metric.infDist (orbit.endpoint k)
                  (DFP.TwoPhaseOrbit.limitCircle Clim Glim)) := by
  obtain ⟨ηDist, hηDist, hDist⟩ :=
    slowCurveEndpointLimitCircleDistanceEquivalent
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηAmp, hηAmp, hAmp⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeTailEquivalent
      p h h_invariant h_pJet h_hJet
  let εbar := min ηDist ηAmp
  have hεbarPos : 0 < εbar := lt_min hηDist.1 hηAmp
  have hεbarLt : εbar < 1 / 4 := (min_le_left _ _).trans_lt hηDist.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεDist : ε₀ ∈ Set.Ioc 0 ηDist :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεAmp : ε₀ ∈ Set.Ioc 0 ηAmp :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  intro Clim hClim Glim hGlim hGlimTendsto
  have hDistance :
      (fun k : ℕ ↦ Metric.infDist (orbit.endpoint k)
          (DFP.TwoPhaseOrbit.limitCircle Clim Glim)) ~[atTop]
        (fun k : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state (k / 2)).ε) := by
    simpa only [orbit] using
      hDist ε₀ hεDist Clim hClim Glim hGlim hGlimTendsto
  have hAmpEq :
      (fun j : ℕ ↦ (orbit.state j).amplitude - Glim) ~[atTop]
        (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε) := by
    simpa only [orbit] using hAmp ε₀ hεAmp Glim hGlim hGlimTendsto
  have hAmpDiffZero :
      Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude - Glim) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ Glim) atTop (𝓝 Glim) := tendsto_const_nhds
    simpa only [orbit, sub_self] using hGlimTendsto.sub hconst
  have hTargetZero :
      Tendsto (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε)
        atTop (𝓝 0) := hAmpEq.tendsto_nhds hAmpDiffZero
  have hthirteenThirdsNe : (13 / 3 : ℝ) ≠ 0 := by
    norm_num
  have hcoeff : (13 / 3 : ℝ) * Glim ≠ 0 :=
    mul_ne_zero hthirteenThirdsNe (ne_of_gt hGlim)
  have hScaleZero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) := by
    have hscaled := hTargetZero.const_mul (((13 / 3 : ℝ) * Glim)⁻¹)
    simpa only [← mul_assoc, inv_mul_cancel₀ hcoeff, one_mul, mul_zero] using hscaled
  have htwoNe : (2 : ℕ) ≠ 0 := by
    norm_num
  have hdiv : Tendsto (fun k : ℕ ↦ k / 2) atTop atTop :=
    Nat.tendsto_div_const_atTop htwoNe
  have hFlatScaleZero :
      Tendsto (fun k : ℕ ↦ (orbit.state (k / 2)).ε) atTop (𝓝 0) :=
    hScaleZero.comp hdiv
  have hSquareLittleScale :
      (fun k : ℕ ↦ (orbit.state (k / 2)).ε ^ 2) =o[atTop]
        (fun k : ℕ ↦ (orbit.state (k / 2)).ε) := by
    have honeLtTwo : (1 : ℕ) < 2 := by
      norm_num
    have hbase :=
      (Asymptotics.isLittleO_pow_pow honeLtTwo).comp_tendsto hFlatScaleZero
    simpa only [Function.comp_def, pow_one] using hbase
  have hSquareLittleTarget :
      (fun k : ℕ ↦ (orbit.state (k / 2)).ε ^ 2) =o[atTop]
        (fun k : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state (k / 2)).ε) :=
    hSquareLittleScale.const_mul_right hcoeff
  exact hSquareLittleTarget.trans_isEquivalent hDistance.symm

/-- A positive linear lower bound on radial deviation yields the corresponding
quadratic lower bound on distance to a limiting circle when the scale is at most one. -/
private theorem mul_sq_le_infDist_limitCircle_of_mul_le_radialDeviation
    (C x : EuclideanSpace ℝ (Fin 2)) (G c ε : ℝ)
    (hG : 0 < G) (hεNonneg : 0 ≤ ε) (hεOne : ε ≤ 1) (hc : 0 ≤ c)
    (hradial : c * ε ≤ ‖x - C‖ - G) :
    c * ε ^ 2 ≤ Metric.infDist x (limitCircle C G) := by
  have hsquare : ε ^ 2 ≤ ε := by
    nlinarith [sq_nonneg ε]
  have hquadratic : c * ε ^ 2 ≤ c * ε :=
    mul_le_mul_of_nonneg_left hsquare hc
  rw [infDist_limitCircle C G hG]
  exact hquadratic.trans (hradial.trans (le_abs_self _))

/-- Every endpoint of a sufficiently small invariant slow-curve orbit stays at
least a uniform positive multiple of its squared cycle scale from the limiting circle. -/
theorem slowCurveEndpointLimitCircleInfDistUniformLower (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cCircle > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ k : ℕ,
                  cCircle * (orbit.state (k / 2)).ε ^ 2 ≤
                    Metric.infDist (orbit.endpoint k) (limitCircle Clim Glim) := by
  obtain ⟨ηTail, hηTail, ωG, hωGSpec, hTail⟩ :=
    slowCurveAmplitudeTailUniform p h h_invariant h_pJet h_hJet
  obtain ⟨ηRadius, hηRadius, ωR, hωRSpec, hRadius⟩ :=
    slowCurvePhaseRadiusErrorUniform p h h_invariant h_pJet h_hJet
  obtain ⟨ηAmp, hηAmp, Gmin, hGmin, Gmax, hGminMax, hAmp⟩ :=
    slowCurveAmplitudeUniformBounds p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let a : ℝ := (13 / 3) * Gmin
  have hthirteenThirds : (0 : ℝ) < 13 / 3 := by
    norm_num
  have ha : 0 < a := mul_pos hthirteenThirds hGmin
  have haQuarter : 0 < a / 4 := by
    positivity
  have hωGSmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ωG η < a / 4 :=
    (tendsto_order.1 hωGSpec.2.2).2 (a / 4) haQuarter
  have hωRSmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ωR η < a / 4 :=
    (tendsto_order.1 hωRSpec.2.2).2 (a / 4) haQuarter
  let ηCap := min ηTail (min ηRadius (min ηAmp ηGraph))
  have hηCap : 0 < ηCap := by
    dsimp only [ηCap]
    exact lt_min hηTail.1 (lt_min hηRadius.1 (lt_min hηAmp.1 hηGraph.1))
  have hηCapMem : Set.Ioc (0 : ℝ) ηCap ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT hηCap
  obtain ⟨η, hωGη, hωRη, hη⟩ :=
    Filter.Eventually.exists (hωGSmall.and (hωRSmall.and hηCapMem))
  have hηTailMem : η ∈ Set.Ioc 0 ηTail :=
    ⟨hη.1, hη.2.trans (min_le_left _ _)⟩
  have hηRadiusMem : η ∈ Set.Ioc 0 ηRadius :=
    ⟨hη.1, hη.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hηAmpLe : η ≤ ηAmp :=
    hη.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hηGraphLe : η ≤ ηGraph :=
    hη.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hηLt : η < (1 / 4 : ℝ) := hηTailMem.2.trans_lt hηTail.2
  let cCircle := a / 2
  have hcCircle : 0 < cCircle := half_pos ha
  refine ⟨η, ⟨hη.1, hηLt⟩, cCircle, hcCircle, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεTail : ε₀ ∈ Set.Ioc 0 η := hε₀
  have hεRadius : ε₀ ∈ Set.Ioc 0 η := hε₀
  have hεAmp : ε₀ ∈ Set.Ioc 0 ηAmp :=
    ⟨hε₀.1, hε₀.2.trans hηAmpLe⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans hηGraphLe⟩
  obtain ⟨GlimBounded, hGlimBounded, hGlimBoundedTendsto, _⟩ :=
    hAmp ε₀ hεAmp
  intro Clim hClim Glim hGlim hGlimTendsto
  have hGlimEq : GlimBounded = Glim :=
    tendsto_nhds_unique hGlimBoundedTendsto hGlimTendsto
  have hGminGlim : Gmin ≤ Glim := by
    rw [← hGlimEq]
    exact hGlimBounded.1
  have hTailData := hTail η hηTailMem ε₀ hεTail Glim hGlim hGlimTendsto
  have hRadiusData := hRadius η hηRadiusMem ε₀ hεRadius Clim hClim
  have hωGNonneg : 0 ≤ ωG η := hωGSpec.1 η hηTailMem
  have hωRNonneg : 0 ≤ ωR η := hωRSpec.1 η hηRadiusMem
  have hcoordinate (j : ℕ) : (orbit.state j).ε =
      (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hraw := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hraw' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hraw
    simpa only [State.coordinates_def] using congrArg Prod.fst hraw'
  have hscale (j : ℕ) : (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
    obtain ⟨_, hbounds⟩ := hGraph ε₀ hεGraph j
    rw [hcoordinate j]
    exact hbounds
  have hquarterLeOne : (1 / 4 : ℝ) ≤ 1 := by
    norm_num
  have hstructured (j : ℕ) (σ : Fin 2) :
      cCircle * (orbit.state j).ε ^ 2 ≤
        Metric.infDist (orbit.endpoint (2 * j + σ.val))
          (limitCircle Clim Glim) := by
    let e := (orbit.state j).ε
    have hePos : 0 < e := (hscale j).1
    have heLeOne : e ≤ 1 :=
      (hscale j).2.trans (hε₀.2.trans (hηLt.le.trans hquarterLeOne))
    have heSq : e ^ 2 ≤ e := by
      nlinarith [sq_nonneg e]
    have htail := hTailData j
    have hradius := hRadiusData j σ
    have htailLower := (abs_le.mp htail).1
    have hradiusLower := (abs_le.mp hradius).1
    have hcoefficient : a ≤ (13 / 3 : ℝ) * Glim := by
      dsimp only [a]
      exact mul_le_mul_of_nonneg_left hGminGlim hthirteenThirds.le
    have hlead : a * e ≤ (13 / 3 : ℝ) * Glim * e :=
      mul_le_mul_of_nonneg_right hcoefficient hePos.le
    have hErrG : ωG η * e < (a / 4) * e :=
      mul_lt_mul_of_pos_right hωGη hePos
    have hErrRLe : ωR η * e ^ 2 ≤ ωR η * e :=
      mul_le_mul_of_nonneg_left heSq hωRNonneg
    have hErrR : ωR η * e < (a / 4) * e :=
      mul_lt_mul_of_pos_right hωRη hePos
    have hlinear : (a / 2) * e ≤
        ‖orbit.endpoint (2 * j + σ.val) - Clim‖ - Glim := by
      dsimp only [e] at htailLower hradiusLower hlead hErrG hErrRLe hErrR ⊢
      nlinarith
    exact mul_sq_le_infDist_limitCircle_of_mul_le_radialDeviation
      Clim (orbit.endpoint (2 * j + σ.val)) Glim cCircle e
      hGlim hePos.le heLeOne hcCircle.le hlinear
  intro k
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · simpa using hstructured j (0 : Fin 2)
  · have hhalf : (2 * j + 1) / 2 = j := by
      omega
    rw [hhalf]
    simpa using hstructured j (1 : Fin 2)

end DFP.TwoPhaseOrbit

namespace DFP.TwoLeg.SlowCurve

/-- Consecutive flattened endpoints of every sufficiently small orbit carried
by an invariant slow curve are at most a constant times the endpoint radius. -/
theorem adjacentEndpointDistanceUpper (curve : SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ C > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ k : ℕ,
          dist (orbit.endpoint k) (orbit.endpoint (k + 1)) ≤
            C * orbit.endpointRadius k := by
  obtain ⟨εbar, hεbar, cStep, hcStep, CStep, hCStep, hStep⟩ :=
    DFP.TwoPhaseOrbit.slowCurvePhaseStepNormUniformBounds
      curve.shape curve.high curve.isInvariant
        curve.shapeRemainder curve.highRemainder
  refine ⟨εbar, hεbar, CStep, hCStep, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  intro k
  have hnorm :
      ‖orbit.endpoint (k + 1) - orbit.endpoint k‖ ≤
        CStep * orbit.endpointRadius k := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · simpa only [Fin.val_zero, add_zero] using
        (hStep ε₀ hε₀ j (0 : Fin 2)).2
    · simpa only [Fin.val_one] using
        (hStep ε₀ hε₀ j (1 : Fin 2)).2
  calc
    dist (orbit.endpoint k) (orbit.endpoint (k + 1)) =
        ‖orbit.endpoint (k + 1) - orbit.endpoint k‖ := by
          rw [dist_eq_norm]
          exact norm_sub_rev _ _
    _ ≤ CStep * orbit.endpointRadius k := hnorm

end DFP.TwoLeg.SlowCurve
