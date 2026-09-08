module

public import ReasLib.Optimization.DFP.TwoPhaseControls.NormJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeBounds
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointCorrection
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepLength

public section

noncomputable section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit

/-- Both normalized phase-step norms are bounded by common positive multiples
of `ε ^ 2` on one neighborhood of the canceled base. -/
private theorem phaseStepNorm_eventually_common_bounds (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∀ᶠ ε in 𝓝 (0 : ℝ),
      (1 / 2 : ℝ) * ε ^ 2 ≤
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).firstStepNorm ∧
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).firstStepNorm ≤
          (5 / 2 : ℝ) * ε ^ 2 ∧
      (1 / 2 : ℝ) * ε ^ 2 ≤
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).secondStepNorm ∧
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).secondStepNorm ≤
          (3 / 2 : ℝ) * ε ^ 2 := by
  have hfirstRemainder :=
    DFP.TwoLeg.NormJet.slowCurveFirstStepRemainder p h hp hh
  have hsecondRemainder :=
    DFP.TwoLeg.NormJet.slowCurveSecondStepRemainder p h hp hh
  have h7little2 : (fun ε : ℝ ↦ ε ^ 7) =o[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 2) :=
    Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 7)
  have h5little2 : (fun ε : ℝ ↦ ε ^ 5) =o[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 2) :=
    Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 5)
  have h6O5 : (fun ε : ℝ ↦ ε ^ 6) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) :=
    (Asymptotics.isLittleO_pow_pow (by norm_num : 5 < 6)).isBigO
  have hfirstPolynomial :
      (fun ε : ℝ ↦
        (2 * ε ^ 2 + (112 / 5) * ε ^ 5 - (11 / 5) * ε ^ 6) -
          2 * ε ^ 2) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    have hsum :=
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)).const_mul_left
          (112 / 5 : ℝ) |>.sub
        (h6O5.const_mul_left (11 / 5 : ℝ))
    refine hsum.congr_left ?_
    intro ε
    ring
  have hsecondPolynomial :
      (fun ε : ℝ ↦
        (ε ^ 2 + (114 / 5) * ε ^ 5 - (49 / 10) * ε ^ 6) -
          ε ^ 2) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    have hsum :=
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)).const_mul_left
          (114 / 5 : ℝ) |>.sub
        (h6O5.const_mul_left (49 / 10 : ℝ))
    refine hsum.congr_left ?_
    intro ε
    ring
  have hfirstLittle :
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).firstStepNorm -
          2 * ε ^ 2) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) := by
    have hsum := hfirstRemainder.trans_isLittleO h7little2 |>.add
      (hfirstPolynomial.trans_isLittleO h5little2)
    refine hsum.congr_left ?_
    intro ε
    ring
  have hsecondLittle :
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).secondStepNorm -
          ε ^ 2) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) := by
    have hsum := hsecondRemainder.trans_isLittleO h7little2 |>.add
      (hsecondPolynomial.trans_isLittleO h5little2)
    refine hsum.congr_left ?_
    intro ε
    ring
  have hfirstBound := hfirstLittle.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hsecondBound := hsecondLittle.bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hfirstBound, hsecondBound] with ε hfirst hsecond
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)] at hfirst hsecond
  have hfirstAbs := abs_le.mp hfirst
  have hsecondAbs := abs_le.mp hsecond
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Uniformly over both phases and every sufficiently small slow-curve orbit,
the physical step norm is bounded above and below by positive multiples of the
endpoint radius. -/
private theorem phaseStepNormUniformBoundsOfData (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε -
        (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cStep > 0, ∃ CStep > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ j : ℕ, ∀ i : Fin 2,
          let k := 2 * j + i.val
          let s := orbit.endpoint (k + 1) - orbit.endpoint k
          let r := orbit.endpointRadius k
          ‖s‖ ∈ Set.Icc (cStep * r) (CStep * r) := by
  have hnormalized :=
    phaseStepNorm_eventually_common_bounds p h h_pJet h_hJet
  obtain ⟨δ, hδ, hnormalizedδ⟩ := Metric.eventually_nhds_iff.mp hnormalized
  obtain ⟨ηAmp, hηAmp, Gmin, hGmin, Gmax, hGminMax, hAmplitude⟩ :=
    slowCurveAmplitudeUniformBounds p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηValid, hηValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity
      p h h_invariant h_pJet h_hJet ηGraph hηGraph
  let εbar := min ηAmp (min ηValid (δ / 2))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηAmp.1 (lt_min hηValid.1 (half_pos hδ))
  have hεbarLt : εbar < 1 / 4 :=
    (min_le_left _ _).trans_lt hηAmp.2
  let cStep := Gmin * (1 / 2)
  let CStep := Gmax * (5 / 2)
  have hcStep : 0 < cStep := mul_pos hGmin (by norm_num)
  have hGmax : 0 < Gmax := hGmin.trans_le hGminMax
  have hCStep : 0 < CStep := mul_pos hGmax (by norm_num)
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, cStep, hcStep, CStep, hCStep, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεAmp : ε₀ ∈ Set.Ioc 0 ηAmp :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεValid : ε₀ ∈ Set.Ioc 0 ηValid := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans
      ((min_le_right _ _).trans ((min_le_left _ _).trans hηValid.2))⟩
  have hεDeltaHalf : ε₀ ≤ δ / 2 :=
    hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Glim, hGlim, hGlimTendsto, hAmplitudeRaw⟩ :=
    hAmplitude ε₀ hεAmp
  have hAmplitudeBound (j : ℕ) :
      (orbit.state j).amplitude ∈ Set.Icc Gmin Gmax := by
    simpa only [orbit] using hAmplitudeRaw j
  have hvalid (j : ℕ) : State.PhaseValidity (orbit.state j) := by
    simpa only [orbit] using hValid ε₀ hεValid j
  have hεcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hc := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hc' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hc
    simpa only [State.coordinates_def] using congrArg Prod.fst hc'
  have hgraphCoordinates (j : ℕ) :
      (orbit.state j).coordinates =
        ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
    obtain ⟨hcoordinateGraph, _⟩ := hGraph ε₀ hεGraph j
    calc
      (orbit.state j).coordinates =
          DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
            simpa only [orbit] using
              DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
      _ = ((DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          p (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          h (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) :=
            hcoordinateGraph
      _ = ((orbit.state j).ε, p (orbit.state j).ε,
          h (orbit.state j).ε) := by rw [hεcoord j]
  have hscale (j : ℕ) : (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
    obtain ⟨_, hs⟩ := hGraph ε₀ hεGraph j
    rw [hεcoord j]
    exact hs
  have hnormalizedState (j : ℕ) :
      (1 / 2 : ℝ) * (orbit.state j).ε ^ 2 ≤
          (DFP.TwoLeg.observableMap
            ((orbit.state j).ε, p (orbit.state j).ε,
              h (orbit.state j).ε)).firstStepNorm ∧
        (DFP.TwoLeg.observableMap
            ((orbit.state j).ε, p (orbit.state j).ε,
              h (orbit.state j).ε)).firstStepNorm ≤
          (5 / 2 : ℝ) * (orbit.state j).ε ^ 2 ∧
      (1 / 2 : ℝ) * (orbit.state j).ε ^ 2 ≤
          (DFP.TwoLeg.observableMap
            ((orbit.state j).ε, p (orbit.state j).ε,
              h (orbit.state j).ε)).secondStepNorm ∧
        (DFP.TwoLeg.observableMap
            ((orbit.state j).ε, p (orbit.state j).ε,
              h (orbit.state j).ε)).secondStepNorm ≤
          (3 / 2 : ℝ) * (orbit.state j).ε ^ 2 := by
    apply hnormalizedδ
    rw [Real.dist_eq, sub_zero, abs_of_pos (hscale j).1]
    exact ((hscale j).2.trans hεDeltaHalf).trans_lt (half_lt_self hδ)
  intro j i
  fin_cases i
  · change ‖orbit.endpoint (2 * j + 1) - orbit.endpoint (2 * j)‖ ∈
      Set.Icc (cStep * orbit.endpointRadius (2 * j))
        (CStep * orbit.endpointRadius (2 * j))
    have hstep : orbit.endpoint (2 * j + 1) - orbit.endpoint (2 * j) =
        (orbit.state j).firstDisplacement := by
      rw [endpoint_odd, endpoint_even, State.middlePoint_def]
      abel
    have hnorm := State.norm_firstDisplacement (orbit.state j) (hvalid j)
    rw [hstep, hnorm, hgraphCoordinates j, endpointRadius_even]
    have ha := hAmplitudeBound j
    have hn := hnormalizedState j
    constructor
    · dsimp only [cStep]
      exact calc
        Gmin * (1 / 2) * (orbit.state j).ε ^ 2 ≤
            (orbit.state j).amplitude * (1 / 2) * (orbit.state j).ε ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right ha.1 (by norm_num))
            (sq_nonneg _)
        _ ≤ (orbit.state j).amplitude *
            (DFP.TwoLeg.observableMap
              ((orbit.state j).ε, p (orbit.state j).ε,
                h (orbit.state j).ε)).firstStepNorm := by
          nlinarith [(hvalid j).amplitude_pos, hn.1]
    · dsimp only [CStep]
      exact calc
        (orbit.state j).amplitude *
            (DFP.TwoLeg.observableMap
              ((orbit.state j).ε, p (orbit.state j).ε,
                h (orbit.state j).ε)).firstStepNorm ≤
            (orbit.state j).amplitude * ((5 / 2) * (orbit.state j).ε ^ 2) :=
          mul_le_mul_of_nonneg_left hn.2.1 (hvalid j).amplitude_pos.le
        _ ≤ Gmax * (5 / 2) * (orbit.state j).ε ^ 2 := by
          nlinarith [ha.2, (hvalid j).amplitude_pos, sq_nonneg (orbit.state j).ε]
  · change ‖orbit.endpoint (2 * j + 1 + 1) - orbit.endpoint (2 * j + 1)‖ ∈
      Set.Icc (cStep * orbit.endpointRadius (2 * j + 1))
        (CStep * orbit.endpointRadius (2 * j + 1))
    have hsucc : orbit.state (j + 1) = (orbit.state j).next := by
      simpa only [orbit] using DFP.TwoPhaseOrbit.ofSlowCurve_succ p h ε₀ j
    have hstep : orbit.endpoint (2 * j + 1 + 1) - orbit.endpoint (2 * j + 1) =
        (orbit.state j).secondDisplacement := by
      have harith : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
      rw [harith, endpoint_even, endpoint_odd, hsucc, State.next_point]
      abel
    have hnorm := State.norm_secondDisplacement (orbit.state j) (hvalid j)
    rw [hstep, hnorm, hgraphCoordinates j, endpointRadius_odd]
    have ha := hAmplitudeBound j
    have hn := hnormalizedState j
    constructor
    · dsimp only [cStep]
      exact calc
        Gmin * (1 / 2) * (orbit.state j).ε ^ 2 ≤
            (orbit.state j).amplitude * (1 / 2) * (orbit.state j).ε ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right ha.1 (by norm_num))
            (sq_nonneg _)
        _ ≤ (orbit.state j).amplitude *
            (DFP.TwoLeg.observableMap
              ((orbit.state j).ε, p (orbit.state j).ε,
                h (orbit.state j).ε)).secondStepNorm := by
          nlinarith [(hvalid j).amplitude_pos, hn.2.2.1]
    · dsimp only [CStep]
      exact calc
        (orbit.state j).amplitude *
            (DFP.TwoLeg.observableMap
              ((orbit.state j).ε, p (orbit.state j).ε,
                h (orbit.state j).ε)).secondStepNorm ≤
            (orbit.state j).amplitude * ((3 / 2) * (orbit.state j).ε ^ 2) :=
          mul_le_mul_of_nonneg_left hn.2.2.2 (hvalid j).amplitude_pos.le
        _ ≤ Gmax * (5 / 2) * (orbit.state j).ε ^ 2 := by
          nlinarith [ha.2, (hvalid j).amplitude_pos, sq_nonneg (orbit.state j).ε]

end DFP.TwoPhaseOrbit

namespace DFP.TwoLeg.SlowCurve

/-- Uniformly over both phases of an invariant slow curve, every physical
step norm is bounded above and below by positive multiples of the endpoint
radius. -/
theorem phaseStepNormUniformBounds (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cStep > 0, ∃ CStep > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ j : ℕ, ∀ i : Fin 2,
          let k := 2 * j + i.val
          let s := orbit.endpoint (k + 1) - orbit.endpoint k
          let r := orbit.endpointRadius k
          ‖s‖ ∈ Set.Icc (cStep * r) (CStep * r) := by
  exact DFP.TwoPhaseOrbit.phaseStepNormUniformBoundsOfData
    curve.shape curve.high curve.isInvariant
      curve.shapeRemainder curve.highRemainder

end DFP.TwoLeg.SlowCurve

namespace DFP.TwoPhaseOrbit

/-- Unbundled compatibility form of
`DFP.TwoLeg.SlowCurve.phaseStepNormUniformBounds`. -/
theorem slowCurvePhaseStepNormUniformBounds (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε -
        (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cStep > 0, ∃ CStep > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ j : ℕ, ∀ i : Fin 2,
          let k := 2 * j + i.val
          let s := orbit.endpoint (k + 1) - orbit.endpoint k
          let r := orbit.endpointRadius k
          ‖s‖ ∈ Set.Icc (cStep * r) (CStep * r) := by
  let curve :=
    DFP.TwoLeg.SlowCurve.ofAsymptotics p h h_pJet h_hJet h_invariant
  have hBounds := DFP.TwoLeg.SlowCurve.phaseStepNormUniformBounds curve
  simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hBounds

end DFP.TwoPhaseOrbit
