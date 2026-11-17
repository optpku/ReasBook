module

public import DFPWolfe.V21.CenterManifold
public import DFPWolfe.V21.CenterInterpolation
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.ParameterizedWolfe
public import ReasLib.Optimization.DFP.DecreaseRatio

public section

noncomputable section

open Filter
open scoped Topology

namespace DFPWolfe.Latest.CenterEndpoints

/-- Helper for cm-center-proposition: simultaneous cancellation of the
leading cubic and quintic center displacements forces the source shape two
and the second off-diagonal control to be minus twice the first. -/
theorem centerControlCancellation {shape firstControl secondControl : ℝ}
    (hshape : 0 < shape) (hfirst : firstControl ≠ 0)
    (hcubic : shape * firstControl + secondControl = 0)
    (hquintic : shape * firstControl + (shape - 1) * secondControl = 0) :
    shape = 2 ∧ secondControl = -2 * firstControl := by
  have hsecond : secondControl = -shape * firstControl := by linarith
  rw [hsecond] at hquintic
  have hproduct : (shape * firstControl) * (2 - shape) = 0 := by
    nlinarith [hquintic]
  have hnonzero : shape * firstControl ≠ 0 := mul_ne_zero hshape.ne' hfirst
  have hshapeEq := (mul_eq_zero.mp hproduct).resolve_left hnonzero
  constructor
  · linarith
  · nlinarith [hsecond]

/-- Helper for cm-limiting-scales: the translated quadratic endpoint values
have the exact decrease ratio before any interpolation is constructed. -/
theorem quadraticEndpointRatio_identity (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ)
    (hq : 0 < -inner ℝ (orbit.endpointGradient k)
      (orbit.endpoint (k + 1) - orbit.endpoint k)) :
    (((1 / 2 : ℝ) * ‖orbit.endpoint k - C‖ ^ 2) -
      ((1 / 2 : ℝ) * ‖orbit.endpoint (k + 1) - C‖ ^ 2)) /
      (-inner ℝ (orbit.endpointGradient k) (orbit.endpoint (k + 1) - orbit.endpoint k)) =
      1 - ‖orbit.endpoint (k + 1) - orbit.endpoint k‖ ^ 2 /
        (2 * (-inner ℝ (orbit.endpointGradient k) (orbit.endpoint (k + 1) - orbit.endpoint k))) +
      inner ℝ (orbit.endpointCorrection C k) (orbit.endpoint (k + 1) - orbit.endpoint k) /
        (-inner ℝ (orbit.endpointGradient k) (orbit.endpoint (k + 1) - orbit.endpoint k)) := by
  have hgradient : orbit.endpoint k - C =
      orbit.endpointGradient k - orbit.endpointCorrection C k := by
    rw [DFP.TwoPhaseOrbit.endpointCorrection_def]
    abel
  exact DFP.decreaseRatio_eq_one_sub_normSq_add_correction
    (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2) C (orbit.endpoint k)
    (orbit.endpoint (k + 1)) (orbit.endpointGradient k) (orbit.endpointCorrection C k)
    rfl rfl hgradient hq

/-- Helper for cm-limiting-scales: both quadratic endpoint decrease ratios
have the source uniform linear remainder around `1 − ϛᵢ/2`. The estimate
concerns the prescribed values and gradients before interpolation. -/
theorem quadraticEndpointRatioErrors (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ K > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ C : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j ↦ (orbit.state j).center) atTop (𝓝 C) →
          ∀ j : ℕ, ∀ i : Fin 2,
            let k := 2 * j + i.val
            let q := -inner ℝ (orbit.endpointGradient k)
              (orbit.endpoint (k + 1) - orbit.endpoint k)
            0 < q ∧
              |(((1 / 2 : ℝ) * ‖orbit.endpoint k - C‖ ^ 2 -
                (1 / 2 : ℝ) * ‖orbit.endpoint (k + 1) - C‖ ^ 2) / q) -
                (1 - (TwoPhaseControls.phase (orbit.state j).ε i).tau / 2)| ≤
                K * (orbit.state j).ε := by
  obtain ⟨ηQ, hηQ, cQ, hcQ, CQ, hCQ, hQ⟩ :=
    DFP.TwoLeg.SlowCurve.phasePredictedDecreaseUniformBounds curve
  obtain ⟨ηRatio, hηRatio, Kratio, hKratio, hRatio⟩ :=
    DFP.TwoLeg.SlowCurve.phaseStepRatioUniformBound curve
  obtain ⟨ηCorr, hηCorr, Kcorr, hKcorr, hCorr⟩ :=
    DFP.TwoLeg.SlowCurve.phaseCorrectionRatioUniformBound curve
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  let εbar := min ηQ (min ηRatio (min ηCorr ηGraph))
  have hεbar : εbar ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor
    · exact lt_min hηQ.1 (lt_min hηRatio.1 (lt_min hηCorr.1 hηGraph.1))
    · exact (min_le_left _ _).trans_lt hηQ.2
  have hK : 0 < Kratio / 2 + Kcorr := by positivity
  refine ⟨εbar, hεbar, Kratio / 2 + Kcorr, hK, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεQ : ε₀ ∈ Set.Ioc (0 : ℝ) ηQ :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεRatio : ε₀ ∈ Set.Ioc (0 : ℝ) ηRatio :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεCorr : ε₀ ∈ Set.Ioc (0 : ℝ) ηCorr :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hεGraph : ε₀ ∈ Set.Ioc (0 : ℝ) ηGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))⟩
  intro Clim hClim j i
  let k := 2 * j + i.val
  let s := orbit.endpoint (k + 1) - orbit.endpoint k
  let q := -inner ℝ (orbit.endpointGradient k) s
  let r := orbit.endpointRadius k
  let εj := (orbit.state j).ε
  have hcoord :
      (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, curve.shape ε₀, curve.high ε₀) := by
    simpa only [orbit] using
      DFP.TwoPhaseOrbit.ofSlowCurve_coordinates curve.shape curve.high ε₀ j
  have hεeq :
      εj = (DFP.TwoLeg.stateMap^[j] (ε₀, curve.shape ε₀, curve.high ε₀)).1 := by
    dsimp only [εj]
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hcoord
  have hεjMem : εj ∈ Set.Ioc (0 : ℝ) ε₀ := by
    rw [hεeq]
    exact (hGraph ε₀ hεGraph j).2
  have hkdiv : k / 2 = j := by
    dsimp only [k]
    fin_cases i
    · omega
    · omega
  have hr : r = εj ^ 2 := by
    dsimp only [r, εj]
    rw [DFP.TwoPhaseOrbit.endpointRadius_def, hkdiv]
  have hqBounds :
      q ∈ Set.Icc (cQ * r ^ 2) (CQ * r ^ 2) := by
    have hraw := hQ ε₀ hεQ j i
    simpa only [orbit, k, s, q, r] using hraw
  have hrPos : 0 < r := by
    rw [hr]
    exact pow_pos hεjMem.1 2
  have hqPos : 0 < q :=
    (mul_pos hcQ (pow_pos hrPos 2)).trans_le hqBounds.1
  have hstepRatio :
      |‖s‖ ^ 2 / q - (TwoPhaseControls.phase εj i).tau| ≤ Kratio * εj := by
    have hraw := hRatio ε₀ hεRatio j i
    simpa only [orbit, k, s, q, εj] using hraw
  have hcorrRatio :
      |inner ℝ (orbit.endpointCorrection Clim k) s / q| ≤ Kcorr * εj := by
    have hraw := hCorr ε₀ hεCorr Clim hClim j i
    simpa only [orbit, k, s, q, εj] using hraw
  have hidentity :
      (((1 / 2 : ℝ) * ‖orbit.endpoint k - Clim‖ ^ 2) -
          ((1 / 2 : ℝ) * ‖orbit.endpoint (k + 1) - Clim‖ ^ 2)) / q =
        1 - ‖s‖ ^ 2 / (2 * q) +
          inner ℝ (orbit.endpointCorrection Clim k) s / q := by
    simpa only [s, q] using
      quadraticEndpointRatio_identity orbit Clim k hqPos
  constructor
  · exact hqPos
  · rw [hidentity]
    have hstep := abs_le.mp hstepRatio
    have hcorr := abs_le.mp hcorrRatio
    have hhalf : ‖s‖ ^ 2 / (2 * q) = (‖s‖ ^ 2 / q) / 2 := by
      field_simp [hqPos.ne']
    rw [hhalf]
    apply abs_le.mpr
    constructor
    · nlinarith [hstep.2, hcorr.1]
    · nlinarith [hstep.1, hcorr.2]

/-- Helper for cm-limiting-scales: every Armijo coefficient below two thirds
is satisfied by the actual quadratic endpoint values, with no support radii
or separation premise. The threshold is uniform along the entire orbit. -/
theorem quadraticEndpointArmijoRatios
    (curve : DFP.TwoLeg.SlowCurve) {c₁ : ℝ}
    (_hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ j : ℕ, ∀ i : Fin 2,
            let k := 2 * j + i.val
            let s := orbit.endpoint (k + 1) - orbit.endpoint k
            let q := -inner ℝ (orbit.endpointGradient k) s
            0 < q ∧ c₁ ≤
              (((1 / 2 : ℝ) * ‖orbit.endpoint k - Clim‖ ^ 2) -
                ((1 / 2 : ℝ) * ‖orbit.endpoint (k + 1) - Clim‖ ^ 2)) / q := by
  obtain ⟨ηE, hηE, K, hK, herrors⟩ := quadraticEndpointRatioErrors curve
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  let margin := (2 / 3 : ℝ) - c₁
  have hmargin : 0 < margin := sub_pos.mpr hc₁_lt_two_thirds
  let εbar := min ηE (min ηGraph (margin / K))
  have hεbar : εbar ∈ Set.Ioo (0 : ℝ) (1 / 4) :=
    ⟨lt_min hηE.1 (lt_min hηGraph.1 (div_pos hmargin hK)),
      (min_le_left _ _).trans_lt hηE.2⟩
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hE : ε₀ ∈ Set.Ioc (0 : ℝ) ηE := ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hGraphStart : ε₀ ∈ Set.Ioc (0 : ℝ) ηGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hsmall : ε₀ ≤ margin / K :=
    hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  intro C hC j i
  have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates curve.shape curve.high ε₀ j
  have hscale : (orbit.state j).ε ≤ ε₀ := by
    have h := (hGraph ε₀ hGraphStart j).2.2
    simpa only [orbit, ← hcoord, DFP.TwoPhaseOrbit.State.coordinates_def] using h
  have herror := herrors ε₀ hE C hC j i
  have hbound : K * (orbit.state j).ε ≤ margin := by
    have h := (le_div_iff₀ hK).mp hsmall
    nlinarith [mul_le_mul_of_nonneg_left hscale hK.le]
  have htau : (TwoPhaseControls.phase (orbit.state j).ε i).tau ≤ (2 / 3 : ℝ) := by
    rcases TwoPhaseControls.phase_tau_mem (orbit.state j).ε i with h | h
    · rw [h]
    · rw [h]
      norm_num
  refine ⟨herror.1, ?_⟩
  have hlower := (abs_le.mp herror.2).1
  dsimp only [margin] at hbound
  linarith

/-- Helper for cm-limiting-scales: the normalized decrease of the prescribed
translated quadratic values at one actual endpoint step. -/
def quadraticDecreaseRatio (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) : ℝ :=
  ((1 / 2 : ℝ) * ‖orbit.endpoint k - C‖ ^ 2 -
    (1 / 2 : ℝ) * ‖orbit.endpoint (k + 1) - C‖ ^ 2) /
      (-inner ℝ (orbit.endpointGradient k) (orbit.endpoint (k + 1) - orbit.endpoint k))

/-- Helper for cm-limiting-scales: the two exact limiting quadratic
endpoint decrease ratios are two thirds and five sixths. -/
def phaseDecreaseLimit (i : Fin 2) : ℝ := if i = 0 then 2 / 3 else 5 / 6

/-- Helper for cm-limiting-scales: the limiting ratios are the source
expressions `1 − ϛᵢ/2` at either phase, independent of scale. -/
theorem phaseDecreaseLimit_eq (ε : ℝ) (i : Fin 2) :
    phaseDecreaseLimit i = 1 - (TwoPhaseControls.phase ε i).tau / 2 := by
  fin_cases i
  · norm_num [phaseDecreaseLimit, TwoPhaseControls.phase_zero, TwoPhaseControls.first_tau]
  · norm_num [phaseDecreaseLimit, TwoPhaseControls.phase_one, TwoPhaseControls.second_tau]

/-- Helper for cm-limiting-scales: a linear remainder bound and vanishing
cycle scale give the precise phase limit of the actual quadratic values. -/
theorem quadraticDecreaseRatio_tendsto (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (K : ℝ) (i : Fin 2)
    (hscale : Tendsto (fun j ↦ (orbit.state j).ε) atTop (𝓝 0))
    (herr : ∀ j, |quadraticDecreaseRatio orbit C (2 * j + i.val) -
      phaseDecreaseLimit i| ≤ K * (orbit.state j).ε) :
    Tendsto (fun j ↦ quadraticDecreaseRatio orbit C (2 * j + i.val))
      atTop (𝓝 (phaseDecreaseLimit i)) := by
  have hbound : Tendsto (fun j ↦ K * (orbit.state j).ε) atTop (𝓝 0) := by
    simpa only [mul_zero] using hscale.const_mul K
  apply tendsto_sub_nhds_zero_iff.mp
  exact squeeze_zero_norm (fun j ↦ (Real.norm_eq_abs _).trans_le (herr j)) hbound

/-- Helper for cm-limiting-scales: one chosen source orbit carries the
pure quadratic endpoint expansion, both phase limits and Wolfe inequalities.
No support or interpolation assumption occurs in this record. -/
structure EndpointProperties (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (c1 c2 K : ℝ) : Prop where
  /-- Helper for cm-limiting-scales: both phase remainders have one linear bound. -/
  ratioErrors : ∀ j (i : Fin 2),
    |quadraticDecreaseRatio orbit C (2 * j + i.val) - phaseDecreaseLimit i| ≤
      K * (orbit.state j).ε
  /-- Helper for cm-limiting-scales: the normalized decreases tend to two thirds and five sixths. -/
  ratioLimits : ∀ i : Fin 2,
    Tendsto (fun j ↦ quadraticDecreaseRatio orbit C (2 * j + i.val))
      atTop (𝓝 (phaseDecreaseLimit i))
  /-- Helper for cm-limiting-scales: each step is a descent step
  with the requested Armijo margin. -/
  armijoRatios : ∀ k,
    0 < -inner ℝ (orbit.endpointGradient k) (orbit.endpoint (k + 1) - orbit.endpoint k) ∧
      c1 ≤ quadraticDecreaseRatio orbit C k
  /-- Helper for cm-limiting-scales: the actual prescribed endpoint gradients
  satisfy strong curvature. -/
  strongCurvature : ∀ k,
    |inner ℝ (orbit.endpointGradient (k + 1)) (orbit.endpoint (k + 1) - orbit.endpoint k)| ≤
      c2 * |inner ℝ (orbit.endpointGradient k) (orbit.endpoint (k + 1) - orbit.endpoint k)|

/-- Helper for cm-limiting-scales: the positive-denominator ratio certificate
is the literal Armijo inequality for the prescribed quadratic endpoint values. -/
theorem EndpointProperties.armijo {orbit : DFP.TwoPhaseOrbit}
    {C : EuclideanSpace ℝ (Fin 2)} {c1 c2 K : ℝ}
    (h : EndpointProperties orbit C c1 c2 K) (k : ℕ) :
    (1 / 2 : ℝ) * ‖orbit.endpoint (k + 1) - C‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖orbit.endpoint k - C‖ ^ 2 +
        c1 * inner ℝ (orbit.endpointGradient k)
          (orbit.endpoint (k + 1) - orbit.endpoint k) := by
  have hratio := (h.armijoRatios k).2
  rw [quadraticDecreaseRatio] at hratio
  have hproduct := (le_div_iff₀ (h.armijoRatios k).1).mp hratio
  linarith

/-- Helper for cm-limiting-scales: every Wolfe pair in the independent
center-manifold range has a single actual source family with uniform quadratic
endpoint remainders and all endpoint Wolfe inequalities before interpolation.
The same family retains its source initialization, exact cycles and limiting circle. -/
theorem sourceFamilyWithEndpointProperties (c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc1upper : c1 < 2 / 3) (hc2 : 2 / 3 ≤ c2) :
    ∃ curve : DFP.TwoLeg.SlowCurve,
      ContDiffAt ℝ 7 (fun ε ↦ (curve.shape ε, curve.high ε)) 0 ∧
      (curve.shape 0, curve.high 0) = (2, 1) ∧
      ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cR > 0, ∃ CR > 0, ∃ Ca > 0, ∃ K > 0,
        ∀ ε₀ ∈ Set.Ioc 0 εbar, ∃ G > 0, ∃ C : EuclideanSpace ℝ (Fin 2),
          DFPWolfe.V21.CenterInterpolation.TrajectoryEstimates curve ε₀ G C cR CR Ca ∧
          EndpointProperties (DFPWolfe.V21.CenterInterpolation.sourceOrbit curve ε₀) C c1 c2 K := by
  obtain ⟨curve, hsmooth, hbase, ηT, hηT, cR, hcR, CR, hCR, Ca, hCa, hfamily⟩ :=
    DFPWolfe.V21.CenterInterpolation.sourceTrajectoryFamily
  obtain ⟨ηE, hηE, K, hK, herrors⟩ := quadraticEndpointRatioErrors curve
  obtain ⟨ηA, hηA, harmijo⟩ := quadraticEndpointArmijoRatios curve hc1 hc1upper
  let εbar := min ηT (min ηE ηA)
  have hεbar : εbar ∈ Set.Ioo (0 : ℝ) (1 / 4) :=
    ⟨lt_min hηT.1 (lt_min hηE.1 hηA.1), (min_le_left _ _).trans_lt hηT.2⟩
  refine ⟨curve, hsmooth, hbase, εbar, hεbar, cR, hcR, CR, hCR, Ca, hCa, K, hK, ?_⟩
  intro ε₀ hε₀
  have hT : ε₀ ∈ Set.Ioc (0 : ℝ) ηT := ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hE : ε₀ ∈ Set.Ioc (0 : ℝ) ηE :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hA : ε₀ ∈ Set.Ioc (0 : ℝ) ηA :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨G, hG, C, htrajectory⟩ := hfamily ε₀ hT
  let orbit := DFPWolfe.V21.CenterInterpolation.sourceOrbit curve ε₀
  have hcenter : Tendsto
      (fun j ↦ ((DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).state j).center)
      atTop (𝓝 C) := by
    simpa only [DFPWolfe.V21.CenterInterpolation.sourceOrbit_def] using htrajectory.centerLimit
  have herror (j : ℕ) (i : Fin 2) :
      |quadraticDecreaseRatio orbit C (2 * j + i.val) - phaseDecreaseLimit i| ≤
        K * (orbit.state j).ε := by
    simpa only [quadraticDecreaseRatio, orbit,
      DFPWolfe.V21.CenterInterpolation.sourceOrbit_def,
      phaseDecreaseLimit_eq ((DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).state j).ε i]
      using (herrors ε₀ hE C hcenter j i).2
  have hscale : Tendsto (fun j ↦ (orbit.state j).ε) atTop (𝓝 0) := by
    have heq (j : ℕ) : (2 * j) / 2 = j := by omega
    have hindices : Tendsto (fun j : ℕ ↦ 2 * j) atTop atTop := by
      apply tendsto_atTop_mono _ tendsto_id
      intro j
      dsimp only [id]
      omega
    simpa only [Function.comp_def, heq] using
      htrajectory.scaleLimit.comp (hindices)
  refine ⟨G, hG, C, htrajectory, ?_⟩
  constructor
  · exact herror
  · intro i
    exact quadraticDecreaseRatio_tendsto orbit C K i hscale (fun j ↦ herror j i)
  · intro k
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · simpa only [quadraticDecreaseRatio, orbit,
        DFPWolfe.V21.CenterInterpolation.sourceOrbit_def, Fin.val_zero, add_zero] using
        harmijo ε₀ hA C hcenter j (0 : Fin 2)
    · simpa only [quadraticDecreaseRatio, orbit,
        DFPWolfe.V21.CenterInterpolation.sourceOrbit_def, Fin.val_one] using
        harmijo ε₀ hA C hcenter j (1 : Fin 2)
  · exact DFP.TwoPhaseOrbit.endpointStrongCurvature_inequality_of_ge_two_thirds
      orbit htrajectory.exactCycles hc2

end DFPWolfe.Latest.CenterEndpoints
