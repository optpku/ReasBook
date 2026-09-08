module

import ReasLib.LinearAlgebra.Matrix.OrthogonalTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.NormJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.OrbitBounds
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeLimit
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseOrbit

public section

open Filter
open scoped Asymptotics Topology

/-- A nonzero low-eigenvector normalization denominator gives a special orthogonal
two-dimensional eigenframe. -/
private theorem frame_mem_specialOrthogonal_of_lowDenom_ne_zero (a b d : ℝ)
    (hdenom : RealSymmetric2.lowDenom a b d ≠ 0) :
    EuclideanPlane.frame (RealSymmetric2.lowVector a b d) ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [EuclideanPlane.frame_mem_specialOrthogonalGroup_iff]
  have hdenomNonneg : 0 ≤ RealSymmetric2.lowDenom a b d := by
    unfold RealSymmetric2.lowDenom
    positivity
  have hdenomPos : 0 < RealSymmetric2.lowDenom a b d :=
    lt_of_le_of_ne hdenomNonneg (Ne.symm hdenom)
  have hraw : ‖RealSymmetric2.lowRaw a b d‖ ≠ 0 := by
    rw [← RealSymmetric2.lowDenom_eq_norm_lowRaw]
    exact hdenom
  rw [RealSymmetric2.lowVector, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hdenomPos, RealSymmetric2.lowDenom_eq_norm_lowRaw]
  exact inv_mul_cancel₀ hraw

/-- Scaling the input gradient by a nonzero real scalar scales the raw DFP displacement
by the same scalar. -/
private theorem rawDisplacement_smul {n : Type*} [Fintype n]
    (H A : Matrix n n ℝ) (g : n → ℝ) (τ G : ℝ) (hG : G ≠ 0) :
    let v := H.mulVec g
    let α := τ * (g ⬝ᵥ v) / (v ⬝ᵥ (A.mulVec v))
    let gG := G • g
    let vG := H.mulVec gG
    let αG := τ * (gG ⬝ᵥ vG) / (vG ⬝ᵥ (A.mulVec vG))
    (- (αG • vG)) = G • (- (α • v)) := by
  dsimp only
  rw [Matrix.mulVec_smul]
  simp only [smul_dotProduct, dotProduct_smul, Matrix.mulVec_smul]
  have hGsq : G * G ≠ 0 := mul_ne_zero hG hG
  funext i
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hGsq]

namespace DFP.TwoPhaseOrbit.State

/-- The normalization denominator of the first-leg low eigenvector at a physical state. -/
private noncomputable def firstLegFrameDenom (s : State) : ℝ :=
  let M := DFP.FirstLeg.outputMetric s.ε s.p s.h
  RealSymmetric2.lowDenom (M 0 0) (M 0 1) (M 1 1)

/-- The unnormalized low-frame coordinate of the first-leg output gradient. -/
private noncomputable def firstLegGradientLowNumerator (s : State) : ℝ :=
  let M := DFP.FirstLeg.outputMetric s.ε s.p s.h
  let g := DFP.FirstLeg.outputGradient s.ε s.p s.h
  (M 1 1 - RealSymmetric2.low (M 0 0) (M 0 1) (M 1 1)) * g 0 - M 0 1 * g 1

/-- The removable first-leg low gradient factor is its raw low coordinate divided by
the low-eigenvector normalization denominator. -/
private theorem firstLegGradientLow_eq_div (s : State) :
    (DFP.FirstLeg.gradientFactors s.ε s.p s.h).1 =
      firstLegGradientLowNumerator s / firstLegFrameDenom s := by
  simp [firstLegGradientLowNumerator, firstLegFrameDenom,
    DFP.FirstLeg.gradientFactors, DFP.FirstLeg.outputMetric,
    DFP.FirstLeg.outputGradient]
  ring

/-- The first-leg eigenframe of a valid phase is special orthogonal. -/
private theorem firstLegFrame_mem_specialOrthogonal (s : State) (h : PhaseValidity s) :
    DFP.FirstLeg.frame s.ε s.p s.h ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  have hdenom : firstLegFrameDenom s ≠ 0 := by
    intro hzero
    have hfactor := h.firstGradientLow_pos
    rw [firstLegGradientLow_eq_div, hzero, div_zero] at hfactor
    exact lt_irrefl 0 hfactor
  let M := DFP.FirstLeg.outputMetric s.ε s.p s.h
  change EuclideanPlane.frame
      (RealSymmetric2.lowVector (M 0 0) (M 0 1) (M 1 1)) ∈
    Matrix.specialOrthogonalGroup (Fin 2) ℝ
  exact frame_mem_specialOrthogonal_of_lowDenom_ne_zero
    (M 0 0) (M 0 1) (M 1 1) hdenom

/-- For a valid physical phase, the first displacement norm is the positive
amplitude times its normalized two-leg observable. -/
theorem norm_firstDisplacement (s : State) (h : PhaseValidity s) :
    ‖s.firstDisplacement‖ =
      s.amplitude * (DFP.TwoLeg.observableMap s.coordinates).firstStepNorm := by
  let H : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.diagonal ![s.h * s.p * s.ε ^ 4, s.h]
  let g₀ : Fin 2 → ℝ := ![(1 : ℝ), s.p * s.ε ^ 2]
  let A := (TwoPhaseControls.first s.ε).matrix
  let τ := (TwoPhaseControls.first s.ε).tau
  have hscale := rawDisplacement_smul H A g₀ τ s.amplitude
    (ne_of_gt h.amplitude_pos)
  have hobservable := congrArg Prod.fst
    (DFP.TwoLeg.observableMap_stepNorms s.ε s.p s.h)
  simp only [] at hobservable
  rw [State.firstDisplacement_def]
  dsimp only
  rw [Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
    s.frame h.frame_specialOrthogonal]
  change ‖WithLp.toLp 2
      (- ((τ * ((s.amplitude • g₀) ⬝ᵥ (H.mulVec (s.amplitude • g₀))) /
          ((H.mulVec (s.amplitude • g₀)) ⬝ᵥ
            (A.mulVec (H.mulVec (s.amplitude • g₀))))) •
        (H.mulVec (s.amplitude • g₀))))‖ =
    s.amplitude * (DFP.TwoLeg.observableMap s.coordinates).firstStepNorm
  rw [hscale]
  rw [WithLp.toLp_smul, norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos h.amplitude_pos]
  rw [State.coordinates_def]
  rw [hobservable]

/-- For a valid physical phase, the second displacement norm is the positive
amplitude times its normalized two-leg observable. -/
theorem norm_secondDisplacement (s : State) (h : PhaseValidity s) :
    ‖s.secondDisplacement‖ =
      s.amplitude * (DFP.TwoLeg.observableMap s.coordinates).secondStepNorm := by
  let spectral := DFP.FirstLeg.spectralFactors s.ε s.p s.h
  let gradient := DFP.FirstLeg.gradientFactors s.ε s.p s.h
  let H : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.diagonal ![s.ε ^ 4 * spectral.1, spectral.2]
  let g₀ : Fin 2 → ℝ := ![gradient.1, s.ε ^ 2 * gradient.2]
  let A := (TwoPhaseControls.second s.ε).matrix
  let τ := (TwoPhaseControls.second s.ε).tau
  have hscale := rawDisplacement_smul H A g₀ τ s.amplitude
    (ne_of_gt h.amplitude_pos)
  have hfirstFrame := firstLegFrame_mem_specialOrthogonal s h
  have hmiddleFrame : s.middleFrame ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
    rw [State.middleFrame_def]
    exact mul_mem h.frame_specialOrthogonal hfirstFrame
  have hobservable := congrArg Prod.snd
    (DFP.TwoLeg.observableMap_stepNorms s.ε s.p s.h)
  simp only [] at hobservable
  rw [State.secondDisplacement_def]
  dsimp only
  rw [Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
    s.middleFrame hmiddleFrame]
  change ‖WithLp.toLp 2
      (- ((τ * ((s.amplitude • g₀) ⬝ᵥ (H.mulVec (s.amplitude • g₀))) /
          ((H.mulVec (s.amplitude • g₀)) ⬝ᵥ
            (A.mulVec (H.mulVec (s.amplitude • g₀))))) •
        (H.mulVec (s.amplitude • g₀))))‖ =
    s.amplitude * (DFP.TwoLeg.observableMap s.coordinates).secondStepNorm
  rw [hscale]
  rw [WithLp.toLp_smul, norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos h.amplitude_pos]
  rw [State.coordinates_def, hobservable]
  rw [Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
    (DFP.FirstLeg.frame s.ε s.p s.h) hfirstFrame]

end DFP.TwoPhaseOrbit.State

namespace DFP.TwoPhaseOrbit

/-- Along every sufficiently small invariant slow-curve orbit, the first
physical displacement divided by the amplitude differs from `2 * ε_j ^ 2` by
`o(ε_j ^ 2)`. -/
theorem slowCurveFirstStepNormRemainder (p h : ℝ → ℝ)
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
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      (fun j : ℕ ↦
        ‖(orbit.state j).firstDisplacement‖ / (orbit.state j).amplitude -
          2 * (orbit.state j).ε ^ 2) =o[atTop]
        (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
  obtain ⟨εbarScale, hεbarScale, hScale⟩ :=
    DFP.TwoLeg.slowCurveScaleAsymptotic p h h_invariant h_pJet h_hJet
  have hEighthRange : (1 / 8 : ℝ) ∈ Set.Ioo 0 (1 / 4) := by
    norm_num
  obtain ⟨εbarValid, hεbarValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet
      (1 / 8) hEighthRange
  obtain ⟨εbarGraph, hεbarGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min (min εbarScale εbarValid) εbarGraph
  have hεbar_pos : 0 < εbar := by
    dsimp [εbar]
    exact lt_min (lt_min hεbarScale hεbarValid.1) hεbarGraph.1
  refine ⟨εbar, hεbar_pos, ?_⟩
  intro ε₀ hε₀
  dsimp
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Scale : ε₀ ∈ Set.Ioc 0 εbarScale :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hε₀Valid : ε₀ ∈ Set.Ioc 0 εbarValid :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 εbarGraph :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  have hvalid (j : ℕ) : State.PhaseValidity (orbit.state j) := by
    simpa [orbit] using hValid ε₀ hε₀Valid j
  have hεcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hcoord' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa [orbit, State.coordinates_def] using hcoord
    exact congrArg Prod.fst hcoord'
  have hεzero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) := by
    have hNineHalfPos : (0 : ℝ) < 9 / 2 := by
      norm_num
    have hbase : Tendsto (fun j : ℕ ↦ (9 / 2 : ℝ) * (j : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hNineHalfPos
    have hOneThirdPos : (0 : ℝ) < 1 / 3 := by
      norm_num
    have hpow : Tendsto
        (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) atTop (𝓝 0) := by
      convert (tendsto_rpow_neg_atTop hOneThirdPos).comp hbase using 1
      · funext j
        dsimp [Function.comp_def]
        congr 1
        ring
    have hscale := hScale ε₀ hε₀Scale
    have hstate : Tendsto
        (fun j : ℕ ↦
          (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) atTop (𝓝 0) :=
      hscale.symm.tendsto_nhds hpow
    exact hstate.congr' (Eventually.of_forall (fun j ↦ (hεcoord j).symm))
  have hrem := DFP.TwoLeg.NormJet.slowCurveFirstStepRemainder p h h_pJet h_hJet
  have hTwoLtSeven : (2 : ℕ) < 7 := by
    norm_num
  have hPowSevenLittle :
      (fun ε : ℝ ↦ ε ^ 7) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) :=
    Asymptotics.isLittleO_pow_pow hTwoLtSeven
  have hremLittle :
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).firstStepNorm -
          (2 * ε ^ 2 + (112 / 5) * ε ^ 5 - (11 / 5) * ε ^ 6)) =o[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 2) := by
    exact hrem.trans_isLittleO hPowSevenLittle
  have hremSeq := hremLittle.comp_tendsto hεzero
  have hgraph (j : ℕ) :
      (orbit.state j).coordinates =
        ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
    obtain ⟨hgraph', _⟩ := hGraph ε₀ hε₀Graph j
    calc
      (orbit.state j).coordinates =
          DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
            simpa [orbit] using DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
      _ = ((DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          p (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          h (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) := hgraph'
      _ = ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
        rw [hεcoord j]
  have hpoint (j : ℕ) :
      ‖(orbit.state j).firstDisplacement‖ / (orbit.state j).amplitude -
          2 * (orbit.state j).ε ^ 2 =
        ((DFP.TwoLeg.observableMap
            ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε)).firstStepNorm -
          (2 * (orbit.state j).ε ^ 2 +
            (112 / 5) * (orbit.state j).ε ^ 5 -
            (11 / 5) * (orbit.state j).ε ^ 6)) +
          (112 / 5) * (orbit.state j).ε ^ 5 -
          (11 / 5) * (orbit.state j).ε ^ 6 := by
    have hnorm := State.norm_firstDisplacement (orbit.state j) (hvalid j)
    have hamp : (orbit.state j).amplitude ≠ 0 :=
      ne_of_gt (hvalid j).amplitude_pos
    rw [hnorm, hgraph j]
    field_simp [hamp]
    ring
  have hpow5 : (fun j : ℕ ↦ (112 / 5 : ℝ) * (orbit.state j).ε ^ 5) =o[atTop]
      (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
    have hTwoLtFive : (2 : ℕ) < 5 := by
      norm_num
    have hPowFiveLittle :
        (fun ε : ℝ ↦ ε ^ 5) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) :=
      Asymptotics.isLittleO_pow_pow hTwoLtFive
    have hPowFiveSeq := hPowFiveLittle.comp_tendsto hεzero
    exact hPowFiveSeq.const_mul_left (112 / 5)
  have hpow6 : (fun j : ℕ ↦ -(11 / 5 : ℝ) * (orbit.state j).ε ^ 6) =o[atTop]
      (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
    have hTwoLtSix : (2 : ℕ) < 6 := by
      norm_num
    have hPowSixLittle :
        (fun ε : ℝ ↦ ε ^ 6) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) :=
      Asymptotics.isLittleO_pow_pow hTwoLtSix
    have hPowSixSeq := hPowSixLittle.comp_tendsto hεzero
    exact hPowSixSeq.const_mul_left (-(11 / 5))
  have hsum := hremSeq.add (hpow5.add hpow6)
  have hpointEq (j : ℕ) :
      ((fun ε : ℝ ↦
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).firstStepNorm -
            (2 * ε ^ 2 + (112 / 5) * ε ^ 5 - (11 / 5) * ε ^ 6))
          ((orbit.state j).ε)) +
        ((112 / 5 : ℝ) * (orbit.state j).ε ^ 5 +
          (-(11 / 5 : ℝ) * (orbit.state j).ε ^ 6)) =
      ‖(orbit.state j).firstDisplacement‖ / (orbit.state j).amplitude -
        2 * (orbit.state j).ε ^ 2 := by
    dsimp only [Function.comp_apply]
    convert (hpoint j).symm using 1
    · ring
  have hsum' := hsum.congr_left hpointEq
  simpa [orbit, Function.comp_def] using hsum'

/-- Along every sufficiently small invariant slow-curve orbit, the second
physical displacement divided by the amplitude differs from `ε_j ^ 2` by
`o(ε_j ^ 2)`. -/
theorem slowCurveSecondStepNormRemainder (p h : ℝ → ℝ)
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
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      (fun j : ℕ ↦
        ‖(orbit.state j).secondDisplacement‖ / (orbit.state j).amplitude -
          (orbit.state j).ε ^ 2) =o[atTop]
        (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
  obtain ⟨εbarScale, hεbarScale, hScale⟩ :=
    DFP.TwoLeg.slowCurveScaleAsymptotic p h h_invariant h_pJet h_hJet
  have hEighthRange : (1 / 8 : ℝ) ∈ Set.Ioo 0 (1 / 4) := by
    norm_num
  obtain ⟨εbarValid, hεbarValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet
      (1 / 8) hEighthRange
  obtain ⟨εbarGraph, hεbarGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min (min εbarScale εbarValid) εbarGraph
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min (lt_min hεbarScale hεbarValid.1) hεbarGraph.1
  refine ⟨εbar, hεbarPos, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Scale : ε₀ ∈ Set.Ioc 0 εbarScale :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hε₀Valid : ε₀ ∈ Set.Ioc 0 εbarValid :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 εbarGraph :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  have hvalid (j : ℕ) : State.PhaseValidity (orbit.state j) := by
    simpa only [orbit] using hValid ε₀ hε₀Valid j
  have hεcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hcoord' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hcoord
    rw [State.coordinates_def] at hcoord'
    exact congrArg Prod.fst hcoord'
  have hεzero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) := by
    have hNineHalfPos : (0 : ℝ) < 9 / 2 := by
      norm_num
    have hbase : Tendsto (fun j : ℕ ↦ (9 / 2 : ℝ) * (j : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hNineHalfPos
    have hOneThirdPos : (0 : ℝ) < 1 / 3 := by
      norm_num
    have hpow : Tendsto
        (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3))
        atTop (𝓝 0) := by
      convert (tendsto_rpow_neg_atTop hOneThirdPos).comp hbase using 1
      · funext j
        dsimp only [Function.comp_apply]
        congr 1
        ring
    have hscale := hScale ε₀ hε₀Scale
    have hstate : Tendsto
        (fun j : ℕ ↦
          (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) atTop (𝓝 0) :=
      hscale.symm.tendsto_nhds hpow
    exact hstate.congr' (Eventually.of_forall (fun j ↦ (hεcoord j).symm))
  have hrem := DFP.TwoLeg.NormJet.slowCurveSecondStepRemainder p h h_pJet h_hJet
  have hTwoLtSeven : (2 : ℕ) < 7 := by
    norm_num
  have hPowSevenLittle :
      (fun ε : ℝ ↦ ε ^ 7) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) :=
    Asymptotics.isLittleO_pow_pow hTwoLtSeven
  have hremLittle :
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).secondStepNorm -
          (ε ^ 2 + (114 / 5) * ε ^ 5 - (49 / 10) * ε ^ 6)) =o[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 2) :=
    hrem.trans_isLittleO hPowSevenLittle
  have hremSeq := hremLittle.comp_tendsto hεzero
  have hgraph (j : ℕ) :
      (orbit.state j).coordinates =
        ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
    obtain ⟨hgraphIterate, _⟩ := hGraph ε₀ hε₀Graph j
    have horbitIterate :
        (orbit.state j).coordinates =
          DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using
        DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hiterateState :
        ((DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          p (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          h (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) =
        ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
      rw [hεcoord j]
    exact horbitIterate.trans (hgraphIterate.trans hiterateState)
  have hpoint (j : ℕ) :
      ‖(orbit.state j).secondDisplacement‖ / (orbit.state j).amplitude -
          (orbit.state j).ε ^ 2 =
        ((DFP.TwoLeg.observableMap
            ((orbit.state j).ε, p (orbit.state j).ε,
              h (orbit.state j).ε)).secondStepNorm -
          ((orbit.state j).ε ^ 2 +
            (114 / 5) * (orbit.state j).ε ^ 5 -
            (49 / 10) * (orbit.state j).ε ^ 6)) +
          (114 / 5) * (orbit.state j).ε ^ 5 -
          (49 / 10) * (orbit.state j).ε ^ 6 := by
    have hnorm := State.norm_secondDisplacement (orbit.state j) (hvalid j)
    have hamp : (orbit.state j).amplitude ≠ 0 :=
      ne_of_gt (hvalid j).amplitude_pos
    rw [hnorm, hgraph j]
    field_simp [hamp]
    ring
  have hpow5 :
      (fun j : ℕ ↦ (114 / 5 : ℝ) * (orbit.state j).ε ^ 5) =o[atTop]
        (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
    have hTwoLtFive : (2 : ℕ) < 5 := by
      norm_num
    have hPowFiveLittle :
        (fun ε : ℝ ↦ ε ^ 5) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) :=
      Asymptotics.isLittleO_pow_pow hTwoLtFive
    have hPowFiveSeq := hPowFiveLittle.comp_tendsto hεzero
    exact hPowFiveSeq.const_mul_left (114 / 5)
  have hpow6 :
      (fun j : ℕ ↦ -(49 / 10 : ℝ) * (orbit.state j).ε ^ 6) =o[atTop]
        (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
    have hTwoLtSix : (2 : ℕ) < 6 := by
      norm_num
    have hPowSixLittle :
        (fun ε : ℝ ↦ ε ^ 6) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) :=
      Asymptotics.isLittleO_pow_pow hTwoLtSix
    have hPowSixSeq := hPowSixLittle.comp_tendsto hεzero
    exact hPowSixSeq.const_mul_left (-(49 / 10))
  have hsum := hremSeq.add (hpow5.add hpow6)
  have hpointEq (j : ℕ) :
      ((fun ε : ℝ ↦
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).secondStepNorm -
            (ε ^ 2 + (114 / 5) * ε ^ 5 - (49 / 10) * ε ^ 6))
          ((orbit.state j).ε)) +
        ((114 / 5 : ℝ) * (orbit.state j).ε ^ 5 +
          (-(49 / 10 : ℝ) * (orbit.state j).ε ^ 6)) =
      ‖(orbit.state j).secondDisplacement‖ / (orbit.state j).amplitude -
        (orbit.state j).ε ^ 2 := by
    dsimp only [Function.comp_apply]
    convert (hpoint j).symm using 1
    · ring
  have hsum' := hsum.congr_left hpointEq
  simpa [orbit, Function.comp_def] using hsum'

/-- Along every sufficiently small invariant slow-curve orbit, the series of
the two physical displacement norms in each cycle is not summable. -/
theorem slowCurveTotalStepLengthNotSummable (p h : ℝ → ℝ)
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
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ¬ Summable (fun j : ℕ ↦
        ‖(orbit.state j).firstDisplacement‖ +
          ‖(orbit.state j).secondDisplacement‖) := by
  obtain ⟨εbarFirst, hεbarFirst, hFirst⟩ :=
    slowCurveFirstStepNormRemainder p h h_invariant h_pJet h_hJet
  obtain ⟨εbarAmplitude, hεbarAmplitude, hAmplitude⟩ :=
    slowCurveAmplitudeExistsPositiveLimit p h h_invariant h_pJet h_hJet
  obtain ⟨εbarSquare, hεbarSquare, hSquare⟩ :=
    DFP.TwoLeg.slowCurveScaleSquareNotSummable p h h_invariant h_pJet h_hJet
  let εbar := min (min εbarFirst εbarAmplitude) εbarSquare
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min (lt_min hεbarFirst hεbarAmplitude) hεbarSquare
  refine ⟨εbar, hεbarPos, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀First : ε₀ ∈ Set.Ioc 0 εbarFirst :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hε₀Amplitude : ε₀ ∈ Set.Ioc 0 εbarAmplitude :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hε₀Square : ε₀ ∈ Set.Ioc 0 εbarSquare :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  have hFirstLittle :
      (fun j : ℕ ↦
        ‖(orbit.state j).firstDisplacement‖ / (orbit.state j).amplitude -
          2 * (orbit.state j).ε ^ 2) =o[atTop]
        (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
    simpa only [orbit] using hFirst ε₀ hε₀First
  obtain ⟨Glim, hGlim, hAmplitudeTendsto⟩ := hAmplitude ε₀ hε₀Amplitude
  have hHalfPos : 0 < Glim / 2 := half_pos hGlim
  have hAmplitudeLower : ∀ᶠ j in atTop,
      Glim / 2 < (orbit.state j).amplitude := by
    have hHalfLt : Glim / 2 < Glim := by
      linarith
    exact (tendsto_order.1 hAmplitudeTendsto).1 (Glim / 2) hHalfLt
  have hRemainderBound : ∀ᶠ j in atTop,
      ‖‖(orbit.state j).firstDisplacement‖ / (orbit.state j).amplitude -
          2 * (orbit.state j).ε ^ 2‖ ≤
        ‖(orbit.state j).ε ^ 2‖ := by
    have hOnePos : (0 : ℝ) < 1 := zero_lt_one
    simpa only [one_mul] using hFirstLittle.bound hOnePos
  have hComparison : ∀ᶠ j in atTop,
      ‖(Glim / 2) * (orbit.state j).ε ^ 2‖ ≤
        ‖(orbit.state j).firstDisplacement‖ +
          ‖(orbit.state j).secondDisplacement‖ := by
    filter_upwards [hAmplitudeLower, hRemainderBound] with j hAmpLower hRem
    have hAmplitudePos : 0 < (orbit.state j).amplitude :=
      hHalfPos.trans hAmpLower
    have hScaleSquareNonneg : 0 ≤ (orbit.state j).ε ^ 2 := sq_nonneg _
    have hRemLower :
        -(orbit.state j).ε ^ 2 ≤
          ‖(orbit.state j).firstDisplacement‖ / (orbit.state j).amplitude -
            2 * (orbit.state j).ε ^ 2 := by
      have hAbsLower := (abs_le.mp hRem).1
      simpa only [Real.norm_eq_abs, abs_of_nonneg hScaleSquareNonneg] using hAbsLower
    have hNormalizedLower :
        (orbit.state j).ε ^ 2 ≤
          ‖(orbit.state j).firstDisplacement‖ / (orbit.state j).amplitude := by
      linarith
    have hFirstLower :
        (orbit.state j).ε ^ 2 * (orbit.state j).amplitude ≤
          ‖(orbit.state j).firstDisplacement‖ := by
      exact (le_div_iff₀ hAmplitudePos).mp hNormalizedLower
    have hScaledLower :
        (Glim / 2) * (orbit.state j).ε ^ 2 ≤
          ‖(orbit.state j).firstDisplacement‖ := by
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hHalfPos.le hScaleSquareNonneg)]
    exact hScaledLower.trans (le_add_of_nonneg_right (norm_nonneg _))
  have hεcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hcoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hcoordinates' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hcoordinates
    have hfirst := congrArg Prod.fst hcoordinates'
    simpa only [State.coordinates_def] using hfirst
  have hSquareNotSummable :
      ¬ Summable (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
    simpa only [hεcoord] using hSquare ε₀ hε₀Square
  intro hTotalSummable
  have hScaledSummable :
      Summable (fun j : ℕ ↦ (Glim / 2) * (orbit.state j).ε ^ 2) :=
    hTotalSummable.of_norm_bounded_eventually_nat hComparison
  have hSquareSummable : Summable (fun j : ℕ ↦ (orbit.state j).ε ^ 2) :=
    (summable_mul_left_iff hHalfPos.ne').mp hScaledSummable
  exact hSquareNotSummable hSquareSummable

end DFP.TwoPhaseOrbit
