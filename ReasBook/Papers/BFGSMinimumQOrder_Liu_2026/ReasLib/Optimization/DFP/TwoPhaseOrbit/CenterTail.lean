module

public import ReasLib.Analysis.Asymptotics.SequenceTail
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterDisplacement
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.PowerTail
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeLimit
public import Mathlib.Analysis.Normed.Group.Completeness

public section

open Filter
open scoped Asymptotics BigOperators Topology

namespace DFP.TwoPhaseOrbit

set_option maxHeartbeats 1000000 in
/-- For sufficiently small exact slow-curve orbits, cycle-boundary centers
approach any given limiting center with cubic order in the cycle scale. -/
theorem slowCurveBoundaryCenterTailIsBigO (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          (fun j : ℕ ↦ ‖(orbit.state j).center - Clim‖) =O[atTop]
            (fun j : ℕ ↦ (orbit.state j).ε ^ 3) := by
  obtain ⟨εbarDrift, hεbarDrift, Ccenter, hCcenter, hDrift⟩ :=
    slowCurveFullCenterDrift p h h_invariant h_pJet h_hJet
  obtain ⟨εbarTail, hεbarTail, C₄, hC₄, C₆, hC₆, hTail⟩ :=
    DFP.TwoLeg.slowCurvePowerTailBounds p h h_invariant h_pJet h_hJet
  obtain ⟨εbarValid, hεbarValid, hValid⟩ :=
    ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet
      (1 / 8) (by norm_num)
  obtain ⟨εbarLimit, hεbarLimit, hLimit⟩ :=
    slowCurveAmplitudeExistsPositiveLimit p h h_invariant h_pJet h_hJet
  let εbar := min εbarDrift (min εbarTail (min εbarValid εbarLimit))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hεbarDrift.1
      (lt_min hεbarTail (lt_min hεbarValid.1 hεbarLimit))
  have hεbarLt : εbar < 1 / 4 := by
    exact (min_le_left _ _).trans_lt hεbarDrift.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Drift : ε₀ ∈ Set.Ioc 0 εbarDrift :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hε₀Tail : ε₀ ∈ Set.Ioc 0 εbarTail := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hε₀Valid : ε₀ ∈ Set.Ioc 0 εbarValid := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₀Limit : ε₀ ∈ Set.Ioc 0 εbarLimit := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Glim, hGlim, hGlim_tendsto⟩ := hLimit ε₀ hε₀Limit
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
  have hampBound : ∀ᶠ j : ℕ in atTop,
      (orbit.state j).amplitude ≤ Glim + 1 := by
    have hmem : Set.Iio (Glim + 1) ∈ 𝓝 Glim := by
      exact Iio_mem_nhds (by linarith)
    exact (hGlim_tendsto.eventually hmem).mono (fun _ hj ↦ hj.le)
  let K : ℝ := (Ccenter + 116 / 5) * (Glim + 1)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hincBound : ∀ᶠ j : ℕ in atTop,
      ‖(orbit.state (j + 1)).center - (orbit.state j).center‖ ≤
        K * (orbit.state j).ε ^ 6 := by
    filter_upwards [hampBound] with j hj
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
    have hεlt : (orbit.state j).ε ≤ 1 :=
      (le_of_lt hphase.ε_lt_quarter).trans (by norm_num)
    have hεpow : (orbit.state j).ε ^ 7 ≤ (orbit.state j).ε ^ 6 := by
      calc
        (orbit.state j).ε ^ 7 = (orbit.state j).ε ^ 6 * (orbit.state j).ε := by
          ring
        _ ≤ (orbit.state j).ε ^ 6 * 1 :=
          mul_le_mul_of_nonneg_left hεlt (pow_nonneg hεpos.le 6)
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
                (orbit.state j).lowVector‖ := by
          rw [add_sub_cancel_right]
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
          rw [norm_smul, hlowNorm, mul_one, Real.norm_eq_abs]
          rw [abs_of_nonneg]
          positivity
    have hfirst : Ccenter * (orbit.state j).amplitude * (orbit.state j).ε ^ 7 ≤
        Ccenter * (Glim + 1) * (orbit.state j).ε ^ 6 := by
      calc
        Ccenter * (orbit.state j).amplitude * (orbit.state j).ε ^ 7 ≤
            Ccenter * (orbit.state j).amplitude * (orbit.state j).ε ^ 6 := by
          exact mul_le_mul_of_nonneg_left hεpow
            (mul_nonneg hCcenter.le hampPos.le)
        _ ≤ Ccenter * (Glim + 1) * (orbit.state j).ε ^ 6 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hj hCcenter.le)
            (pow_nonneg hεpos.le 6)
    have hsecond : (116 / 5) * (orbit.state j).amplitude * (orbit.state j).ε ^ 6 ≤
        (116 / 5) * (Glim + 1) * (orbit.state j).ε ^ 6 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hj (by norm_num)) (pow_nonneg hεpos.le 6)
    dsimp only [K]
    calc
      ‖(orbit.state (j + 1)).center - (orbit.state j).center‖ ≤
          Ccenter * (orbit.state j).amplitude * (orbit.state j).ε ^ 7 +
            (116 / 5) * (orbit.state j).amplitude * (orbit.state j).ε ^ 6 := herror
      _ ≤ Ccenter * (Glim + 1) * (orbit.state j).ε ^ 6 +
            (116 / 5) * (Glim + 1) * (orbit.state j).ε ^ 6 :=
        add_le_add hfirst hsecond
      _ = (Ccenter + 116 / 5) * (Glim + 1) * (orbit.state j).ε ^ 6 := by ring
  have hincNorm : Summable (fun j : ℕ ↦
      ‖(orbit.state (j + 1)).center - (orbit.state j).center‖) := by
    refine (hεsix.mul_left K).of_norm_bounded_eventually_nat ?_
    filter_upwards [hincBound] with j hj
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hj
  intro Clim hClim
  exact SequenceTail.norm_sub_limit_isBigO
    (a := fun j ↦ (orbit.state j).center) (aLim := Clim)
    (u := fun j ↦ (orbit.state j).ε ^ 6)
    (v := fun j ↦ (orbit.state j).ε ^ 3)
    (K := K) (C := C₆) hK
    (fun j ↦ pow_nonneg (hvalid j).ε_pos.le 3)
    hincNorm hClim hincBound htailOrbit

/-- For sufficiently small exact slow-curve orbits, intermediate centers
approach the cycle-boundary limit with cubic order in the cycle scale. -/
theorem slowCurveMiddleCenterTailIsBigO (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          (fun j : ℕ ↦ ‖(orbit.state j).middleCenter - Clim‖) =O[atTop]
            (fun j : ℕ ↦ (orbit.state j).ε ^ 3) := by
  obtain ⟨εbarBoundary, hεbarBoundary, hBoundary⟩ :=
    slowCurveBoundaryCenterTailIsBigO p h h_invariant h_pJet h_hJet
  obtain ⟨εbarHalf, hεbarHalf, Chalf, hChalf, hHalf⟩ :=
    slowCurveHalfCenterDisplacementBound p h h_invariant h_pJet h_hJet
  obtain ⟨εbarLimit, hεbarLimit, hLimit⟩ :=
    slowCurveAmplitudeExistsPositiveLimit p h h_invariant h_pJet h_hJet
  obtain ⟨εbarValid, hεbarValid, hValid⟩ :=
    ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet
      (1 / 8) (by norm_num)
  let εbar := min εbarBoundary (min εbarHalf (min εbarLimit εbarValid))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hεbarBoundary.1
      (lt_min hεbarHalf.1 (lt_min hεbarLimit hεbarValid.1))
  have hεbarLt : εbar < 1 / 4 := by
    exact (min_le_left _ _).trans_lt hεbarBoundary.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Boundary : ε₀ ∈ Set.Ioc 0 εbarBoundary :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hε₀Half : ε₀ ∈ Set.Ioc 0 εbarHalf := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hε₀Limit : ε₀ ∈ Set.Ioc 0 εbarLimit := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₀Valid : ε₀ ∈ Set.Ioc 0 εbarValid := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Glim, hGlim, hGlimTendsto⟩ := hLimit ε₀ hε₀Limit
  have hvalid (j : ℕ) : State.PhaseValidity (orbit.state j) := by
    simpa only [orbit] using hValid ε₀ hε₀Valid j
  have hampBound : ∀ᶠ j : ℕ in atTop,
      (orbit.state j).amplitude ≤ Glim + 1 := by
    have hmem : Set.Iio (Glim + 1) ∈ 𝓝 Glim := by
      exact Iio_mem_nhds (by linarith)
    exact (hGlimTendsto.eventually hmem).mono (fun _ hj ↦ hj.le)
  have hhalfO :
      (fun j : ℕ ↦ ‖(orbit.state j).halfCenterDisplacement‖) =O[atTop]
        (fun j : ℕ ↦ (orbit.state j).ε ^ 3) := by
    apply Asymptotics.IsBigO.of_bound (Chalf * (Glim + 1))
    filter_upwards [hampBound] with j hj
    have hhalfJ :
        ‖(orbit.state j).halfCenterDisplacement‖ ≤
          Chalf * (orbit.state j).amplitude * (orbit.state j).ε ^ 3 := by
      simpa only [orbit] using hHalf ε₀ hε₀Half j
    have hraw :
        ‖(orbit.state j).halfCenterDisplacement‖ ≤
          Chalf * (Glim + 1) * (orbit.state j).ε ^ 3 := by
      exact hhalfJ.trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hj hChalf.le)
          (pow_nonneg (hvalid j).ε_pos.le 3))
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (pow_nonneg (hvalid j).ε_pos.le 3)] using hraw
  intro Clim hClim
  have hboundary := hBoundary ε₀ hε₀Boundary Clim hClim
  obtain ⟨Cboundary, hboundaryBound⟩ := hboundary.bound
  obtain ⟨ChalfTail, hhalfBound⟩ := hhalfO.bound
  apply Asymptotics.IsBigO.of_bound (Cboundary + ChalfTail)
  filter_upwards [hboundaryBound, hhalfBound] with j hboundaryJ hhalfJ
  have hidentity :
      (orbit.state j).middleCenter - Clim =
        (orbit.state j).halfCenterDisplacement +
          ((orbit.state j).center - Clim) := by
    rw [State.halfCenterDisplacement_def]
    abel
  calc
    ‖‖(orbit.state j).middleCenter - Clim‖‖ =
        ‖(orbit.state j).middleCenter - Clim‖ := norm_norm _
    _ = ‖(orbit.state j).halfCenterDisplacement +
          ((orbit.state j).center - Clim)‖ := by rw [hidentity]
    _ ≤ ‖(orbit.state j).halfCenterDisplacement‖ +
          ‖(orbit.state j).center - Clim‖ := norm_add_le _ _
    _ = ‖‖(orbit.state j).halfCenterDisplacement‖‖ +
          ‖‖(orbit.state j).center - Clim‖‖ := by simp only [norm_norm]
    _ ≤ ChalfTail * ‖(orbit.state j).ε ^ 3‖ +
          Cboundary * ‖(orbit.state j).ε ^ 3‖ :=
      add_le_add hhalfJ hboundaryJ
    _ = (Cboundary + ChalfTail) * ‖(orbit.state j).ε ^ 3‖ := by ring

end DFP.TwoPhaseOrbit
