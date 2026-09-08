module

public import ReasLib.Analysis.Asymptotics.SequenceTail
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterDisplacement
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.PowerTail
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeBounds
public import Mathlib.Analysis.Normed.Group.Completeness

public section

open Filter
open scoped Asymptotics BigOperators Topology

namespace DFP.TwoPhaseOrbit

set_option maxHeartbeats 1000000 in
-- The quantitative tail calculation expands several nested norm and tsum interfaces.
/-- A single positive constant uniformly controls the boundary and intermediate
center tails of every sufficiently small invariant slow-curve orbit. -/
theorem slowCurveCenterTailUniformBound (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kcenter > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ j : ℕ, ‖(orbit.state j).center - Clim‖ +
                ‖(orbit.state j).middleCenter - Clim‖ ≤
              Kcenter * (orbit.state j).ε ^ 3 := by
  obtain ⟨εbarDrift, hεbarDrift, Ccenter, hCcenter, hDrift⟩ :=
    slowCurveFullCenterDrift p h h_invariant h_pJet h_hJet
  obtain ⟨εbarHalf, hεbarHalf, Chalf, hChalf, hHalf⟩ :=
    slowCurveHalfCenterDisplacementBound p h h_invariant h_pJet h_hJet
  obtain ⟨εbarTail, hεbarTail, C₄, hC₄, C₆, hC₆, hTail⟩ :=
    DFP.TwoLeg.slowCurvePowerTailBounds p h h_invariant h_pJet h_hJet
  obtain ⟨εbarValid, hεbarValid, hValid⟩ :=
    ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet
      (1 / 8) (by norm_num)
  obtain ⟨εbarAmp, hεbarAmp, Gmin, hGmin, Gmax, hGminMax, hAmp⟩ :=
    slowCurveAmplitudeUniformBounds p h h_invariant h_pJet h_hJet
  let εbar := min εbarDrift (min εbarHalf (min εbarTail (min εbarValid εbarAmp)))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hεbarDrift.1
      (lt_min hεbarHalf.1 (lt_min hεbarTail (lt_min hεbarValid.1 hεbarAmp.1)))
  have hεbarLt : εbar < 1 / 4 :=
    (min_le_left _ _).trans_lt hεbarDrift.2
  let K : ℝ := (Ccenter + 116 / 5) * Gmax
  let Kcenter : ℝ := 2 * (K * C₆) + Chalf * Gmax
  have hGmaxPos : 0 < Gmax := lt_of_lt_of_le hGmin hGminMax
  have hcoefPos : 0 < Ccenter + 116 / 5 := by positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg hcoefPos.le hGmaxPos.le
  have hKcenter : 0 < Kcenter := by
    dsimp only [Kcenter]
    have hfirst : 0 ≤ K * C₆ := mul_nonneg hK hC₆.le
    have hsecond : 0 < Chalf * Gmax := mul_pos hChalf hGmaxPos
    nlinarith
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, Kcenter, hKcenter, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Drift : ε₀ ∈ Set.Ioc 0 εbarDrift :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hε₀Half : ε₀ ∈ Set.Ioc 0 εbarHalf := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hε₀Tail : ε₀ ∈ Set.Ioc 0 εbarTail := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₀Valid : ε₀ ∈ Set.Ioc 0 εbarValid := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right εbarDrift _).trans
      ((min_le_right εbarHalf _).trans
        ((min_le_right εbarTail _).trans (min_le_left _ _)))
  have hε₀Amp : ε₀ ∈ Set.Ioc 0 εbarAmp := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right εbarDrift _).trans
      ((min_le_right εbarHalf _).trans
        ((min_le_right εbarTail _).trans (min_le_right _ _)))
  obtain ⟨Glim, hGlim, hGlimTendsto, hampInterval⟩ := hAmp ε₀ hε₀Amp
  have hvalid (j : ℕ) : State.PhaseValidity (orbit.state j) := by
    simpa only [orbit] using hValid ε₀ hε₀Valid j
  have hεcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hcoord' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hcoord
    simpa only [State.coordinates_def] using congrArg Prod.fst hcoord'
  have htailOrbit (j : ℕ) :
      Summable (fun k : ℕ ↦ (orbit.state (j + k)).ε ^ 6) ∧
        (∑' k : ℕ, (orbit.state (j + k)).ε ^ 6) ≤
          C₆ * (orbit.state j).ε ^ 3 := by
    simpa only [hεcoord] using (hTail ε₀ hε₀Tail j).2
  have hεsix : Summable (fun j : ℕ ↦ (orbit.state j).ε ^ 6) := by
    simpa only [zero_add] using (htailOrbit 0).1
  have hampBound (j : ℕ) : (orbit.state j).amplitude ≤ Gmax :=
    (hampInterval j).2
  have hincBound : ∀ j : ℕ,
      ‖(orbit.state (j + 1)).center - (orbit.state j).center‖ ≤
        K * (orbit.state j).ε ^ 6 := by
    intro j
    have hj := hampBound j
    have hphase := hvalid j
    have hDriftJ :
        ‖(orbit.state (j + 1)).center - (orbit.state j).center +
            ((116 / 5) * (orbit.state j).amplitude * (orbit.state j).ε ^ 6) •
              (orbit.state j).lowVector‖ ≤
          Ccenter * (orbit.state j).amplitude * (orbit.state j).ε ^ 7 := by
      simpa only [orbit] using hDrift ε₀ hε₀Drift j
    have hlowNorm : ‖(orbit.state j).lowVector‖ = 1 := by
      have hlowVectorEq : (orbit.state j).lowVector =
          WithLp.toLp 2 (fun i ↦ (orbit.state j).frame i 0) := by
        ext i
        rw [State.lowVector_apply]
      rw [hlowVectorEq]
      exact State.toCycleBoundaryState_e_norm (orbit.state j) hphase
    have hεpos : 0 < (orbit.state j).ε := hphase.ε_pos
    have hampPos : 0 < (orbit.state j).amplitude := hphase.amplitude_pos
    have hεpow : (orbit.state j).ε ^ 7 ≤ (orbit.state j).ε ^ 6 := by
      calc
        (orbit.state j).ε ^ 7 = (orbit.state j).ε ^ 6 * (orbit.state j).ε := by ring
        _ ≤ (orbit.state j).ε ^ 6 * 1 :=
          mul_le_mul_of_nonneg_left
            ((le_of_lt hphase.ε_lt_quarter).trans (by norm_num))
            (pow_nonneg hεpos.le 6)
        _ = (orbit.state j).ε ^ 6 := by ring
    have herror :
        ‖(orbit.state (j + 1)).center - (orbit.state j).center‖ ≤
          Ccenter * (orbit.state j).amplitude * (orbit.state j).ε ^ 7 +
            (116 / 5) * (orbit.state j).amplitude * (orbit.state j).ε ^ 6 := by
      calc
        ‖(orbit.state (j + 1)).center - (orbit.state j).center‖ =
            ‖((orbit.state (j + 1)).center - (orbit.state j).center +
                ((116 / 5) * (orbit.state j).amplitude * (orbit.state j).ε ^ 6) •
                  (orbit.state j).lowVector) -
              ((116 / 5) * (orbit.state j).amplitude * (orbit.state j).ε ^ 6) •
                (orbit.state j).lowVector‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖(orbit.state (j + 1)).center - (orbit.state j).center +
                ((116 / 5) * (orbit.state j).amplitude * (orbit.state j).ε ^ 6) •
                  (orbit.state j).lowVector‖ +
              ‖((116 / 5) * (orbit.state j).amplitude * (orbit.state j).ε ^ 6) •
                (orbit.state j).lowVector‖ := norm_sub_le _ _
        _ ≤ Ccenter * (orbit.state j).amplitude * (orbit.state j).ε ^ 7 +
              ‖((116 / 5) * (orbit.state j).amplitude * (orbit.state j).ε ^ 6) •
                (orbit.state j).lowVector‖ := add_le_add_left hDriftJ _
        _ = Ccenter * (orbit.state j).amplitude * (orbit.state j).ε ^ 7 +
              (116 / 5) * (orbit.state j).amplitude * (orbit.state j).ε ^ 6 := by
          rw [norm_smul, hlowNorm, mul_one, Real.norm_eq_abs, abs_of_nonneg]
          positivity
    have hfirst : Ccenter * (orbit.state j).amplitude * (orbit.state j).ε ^ 7 ≤
        Ccenter * Gmax * (orbit.state j).ε ^ 6 := by
      calc
        Ccenter * (orbit.state j).amplitude * (orbit.state j).ε ^ 7 ≤
            Ccenter * (orbit.state j).amplitude * (orbit.state j).ε ^ 6 :=
          mul_le_mul_of_nonneg_left hεpow (mul_nonneg hCcenter.le hampPos.le)
        _ ≤ Ccenter * Gmax * (orbit.state j).ε ^ 6 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hj hCcenter.le)
            (pow_nonneg hεpos.le 6)
    have hsecond : (116 / 5) * (orbit.state j).amplitude * (orbit.state j).ε ^ 6 ≤
        (116 / 5) * Gmax * (orbit.state j).ε ^ 6 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hj (by norm_num)) (pow_nonneg hεpos.le 6)
    dsimp only [K]
    calc
      ‖(orbit.state (j + 1)).center - (orbit.state j).center‖ ≤
          Ccenter * (orbit.state j).amplitude * (orbit.state j).ε ^ 7 +
            (116 / 5) * (orbit.state j).amplitude * (orbit.state j).ε ^ 6 := herror
      _ ≤ Ccenter * Gmax * (orbit.state j).ε ^ 6 +
            (116 / 5) * Gmax * (orbit.state j).ε ^ 6 :=
        add_le_add hfirst hsecond
      _ = (Ccenter + 116 / 5) * Gmax * (orbit.state j).ε ^ 6 := by ring
  have hincNorm : Summable (fun j : ℕ ↦
      ‖(orbit.state (j + 1)).center - (orbit.state j).center‖) := by
    refine (hεsix.mul_left K).of_norm_bounded_eventually_nat ?_
    filter_upwards [Filter.Eventually.of_forall hincBound] with j hj
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hj
  intro Clim hClim
  have hboundary (j : ℕ) :
      ‖(orbit.state j).center - Clim‖ ≤ K * C₆ * (orbit.state j).ε ^ 3 := by
    exact SequenceTail.norm_sub_limit_le
      (a := fun n ↦ (orbit.state n).center)
      (aLim := Clim) (u := fun n ↦ (orbit.state n).ε ^ 6)
      (v := fun n ↦ (orbit.state n).ε ^ 3) (K := K) (C := C₆)
      hK hincNorm hClim hincBound htailOrbit j
  intro j
  have hampNow : (orbit.state j).amplitude ≤ Gmax := hampBound j
  have hhalfNow :
      ‖(orbit.state j).halfCenterDisplacement‖ ≤
        Chalf * Gmax * (orbit.state j).ε ^ 3 := by
    calc
      ‖(orbit.state j).halfCenterDisplacement‖ ≤
          Chalf * (orbit.state j).amplitude * (orbit.state j).ε ^ 3 := by
            simpa only [orbit] using hHalf ε₀ hε₀Half j
      _ ≤ Chalf * Gmax * (orbit.state j).ε ^ 3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hampNow hChalf.le)
          (pow_nonneg (hvalid j).ε_pos.le 3)
  have hmiddle :
      ‖(orbit.state j).middleCenter - Clim‖ ≤
        ‖(orbit.state j).halfCenterDisplacement‖ +
          ‖(orbit.state j).center - Clim‖ := by
    calc
      ‖(orbit.state j).middleCenter - Clim‖ =
          ‖(orbit.state j).halfCenterDisplacement +
            ((orbit.state j).center - Clim)‖ := by
        rw [State.halfCenterDisplacement_def]
        congr 1
        abel
      _ ≤ ‖(orbit.state j).halfCenterDisplacement‖ +
          ‖(orbit.state j).center - Clim‖ := norm_add_le _ _
  dsimp only [Kcenter]
  calc
    ‖(orbit.state j).center - Clim‖ + ‖(orbit.state j).middleCenter - Clim‖ ≤
        2 * ‖(orbit.state j).center - Clim‖ +
          ‖(orbit.state j).halfCenterDisplacement‖ := by linarith
    _ ≤ 2 * (K * C₆ * (orbit.state j).ε ^ 3) +
          Chalf * Gmax * (orbit.state j).ε ^ 3 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hboundary j) (by norm_num)) hhalfNow
    _ = (2 * (K * C₆) + Chalf * Gmax) * (orbit.state j).ε ^ 3 := by ring

end DFP.TwoPhaseOrbit
