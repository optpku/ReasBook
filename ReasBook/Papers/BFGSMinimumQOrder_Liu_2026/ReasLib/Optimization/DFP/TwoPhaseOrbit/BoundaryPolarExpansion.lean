module

import ReasLib.LinearAlgebra.Matrix.OrthogonalTransport
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterTailUniform
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeBounds
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.BoundaryPolarExpansion.Basic

public section

open Filter
open scoped Asymptotics Matrix Topology

namespace DFP.TwoPhaseOrbit

/-! The boundary expansion proof uses the exact gradient representation together
with the orthogonal transport interface. -/

/-- Helper for Lemma 4.10: the gradient mismatch from the model slope has
the scalar norm `amplitude * |p - 2| * ε²`. -/
private theorem gradient_modelError_norm (s : State) (hs : State.PhaseValidity s) :
    ‖s.gradient - s.amplitude • WithLp.toLp 2
        (s.frame *ᵥ ![(1 : ℝ), 2 * s.ε ^ 2])‖ =
      s.amplitude * |s.p - 2| * s.ε ^ 2 := by
  rw [State.gradient_def]
  have hvector :
      s.amplitude • WithLp.toLp 2
          (s.frame *ᵥ ![(1 : ℝ), s.p * s.ε ^ 2]) -
        s.amplitude • WithLp.toLp 2
          (s.frame *ᵥ ![(1 : ℝ), 2 * s.ε ^ 2]) =
      s.amplitude • WithLp.toLp 2
          (s.frame *ᵥ ![(0 : ℝ), (s.p - 2) * s.ε ^ 2]) := by
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
  rw [hvector, norm_smul, Real.norm_eq_abs, abs_of_pos hs.amplitude_pos]
  rw [Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
    s.frame hs.frame_specialOrthogonal]
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]
  ring

/-- Helper for Lemma 4.10: a vanishing scale is little-o of the
amplitude-weighted quadratic scale whenever the amplitude has a positive lower
bound. -/
private theorem cube_isLittleO_amplitude_square
    {ι : Type*} {l : Filter ι} {ε amplitude : ι → ℝ} {G : ℝ}
    (hεzero : Tendsto ε l (𝓝 0))
    (hεnonneg : ∀ᶠ i in l, 0 ≤ ε i)
    (hamplower : ∀ᶠ i in l, G ≤ amplitude i) (hG : 0 < G) :
    (fun i ↦ ε i ^ 3) =o[l] (fun i ↦ amplitude i * ε i ^ 2) := by
  have hscale : (fun i ↦ ε i ^ 2) =O[l]
      (fun i ↦ amplitude i * ε i ^ 2) := by
    apply Asymptotics.IsBigO.of_bound G⁻¹
    filter_upwards [hεnonneg, hamplower] with i hi hAi
    have hsq : 0 ≤ ε i ^ 2 := sq_nonneg _
    have hprod : 0 ≤ amplitude i * ε i ^ 2 :=
      mul_nonneg (hG.le.trans hAi) hsq
    rw [Real.norm_eq_abs, abs_of_nonneg hsq,
      Real.norm_eq_abs, abs_of_nonneg hprod]
    calc
      ε i ^ 2 = G⁻¹ * (G * ε i ^ 2) := by
        field_simp [ne_of_gt hG]
      _ ≤ G⁻¹ * (amplitude i * ε i ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hAi hsq) (inv_nonneg.mpr hG.le)
  have hsmall : (fun i ↦ ε i) =o[l]
      (fun _i : ι ↦ (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 hεzero
  have hcube := hsmall.mul_isBigO
    (Asymptotics.isBigO_refl (fun i ↦ ε i ^ 2) l)
  have hcube' : (fun i ↦ ε i ^ 3) =o[l]
      (fun i ↦ ε i ^ 2) := by
    refine hcube.congr' (Eventually.of_forall ?_) (Eventually.of_forall ?_)
    · intro i
      ring
    · intro i
      simp
  exact hcube'.trans_isBigO hscale

/-- For an invariant slow-curve orbit with the prescribed shape jets, every
cycle-boundary endpoint differs from its limiting center by the current
amplitude times the physical-frame vector `![1, 2 * ε²]`, up to a remainder
little-o of `amplitude * ε²`. -/
theorem slowCurveBoundaryPolarExpansion (p h : ℝ → ℝ)
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
          (fun j : ℕ ↦
            let s := orbit.state j
            s.point - Clim -
              s.amplitude • WithLp.toLp 2 (s.frame *ᵥ ![(1 : ℝ), 2 * s.ε ^ 2])) =o[atTop]
            (fun j : ℕ ↦
              let s := orbit.state j
              s.amplitude * s.ε ^ 2) := by
  obtain ⟨ηCenter, hηCenter, Kcenter, hKcenter, hCenter⟩ :=
    slowCurveCenterTailUniformBound p h h_invariant h_pJet h_hJet
  obtain ⟨ηAmp, hηAmp, Gmin, hGmin, Gmax, hGminMax, hAmp⟩ :=
    slowCurveAmplitudeUniformBounds p h h_invariant h_pJet h_hJet
  have hOneEighth : (1 / 8 : ℝ) ∈ Set.Ioo 0 (1 / 4) := by
    norm_num
  obtain ⟨ηValid, hηValid, hValid⟩ :=
    ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet
      (1 / 8) hOneEighth
  obtain ⟨ηSum, hηSum, hSum⟩ :=
    DFP.TwoLeg.slowCurveScaleFourthPowerSummable p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min ηCenter (min ηAmp (min ηValid (min ηSum ηGraph)))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηCenter.1
      (lt_min hηAmp.1 (lt_min hηValid.1 (lt_min hηSum hηGraph.1)))
  have hεbarLt : εbar < 1 / 4 := by
    exact (min_le_left _ _).trans_lt hηCenter.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Center : ε₀ ∈ Set.Ioc 0 ηCenter :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hε₀Amp : ε₀ ∈ Set.Ioc 0 ηAmp := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hε₀Valid : ε₀ ∈ Set.Ioc 0 ηValid := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₀Sum : ε₀ ∈ Set.Ioc 0 ηSum := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 ηGraph := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hvalid (j : ℕ) : State.PhaseValidity (orbit.state j) := by
    simpa only [orbit] using hValid ε₀ hε₀Valid j
  have hεcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hc := ofSlowCurve_coordinates p h ε₀ j
    have hc' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hc
    simpa only [State.coordinates_def] using congrArg Prod.fst hc'
  have hgraphCoordinates (j : ℕ) :
      (orbit.state j).coordinates =
        ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
    obtain ⟨hc, _⟩ := hGraph ε₀ hε₀Graph j
    calc
      (orbit.state j).coordinates =
          DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
            simpa only [orbit] using ofSlowCurve_coordinates p h ε₀ j
      _ = ((DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          p (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          h (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) := hc
      _ = ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
        rw [hεcoord j]
  obtain ⟨Glim, hGlim, hAmpTendsto, hAmpInterval⟩ := hAmp ε₀ hε₀Amp
  have hampLower (j : ℕ) : Gmin ≤ (orbit.state j).amplitude := by
    have hIcc := hAmpInterval j
    simpa only [orbit] using hIcc.1
  have hscaleFourth : Summable (fun j : ℕ ↦ (orbit.state j).ε ^ 4) := by
    simpa only [hεcoord] using hSum ε₀ hε₀Sum
  have hscaleZero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε)
      atTop (𝓝 0) := by
    have hpowZero := hscaleFourth.tendsto_atTop_zero
    have hquarterPos : (0 : ℝ) < 1 / 4 := by
      norm_num
    have hfourNe : (4 : ℕ) ≠ 0 := by
      norm_num
    have hroot := hpowZero.rpow_const_nhds_zero hquarterPos
    have hscalePos (j : ℕ) : 0 < (orbit.state j).ε := (hvalid j).ε_pos
    refine hroot.congr' (Eventually.of_forall ?_)
    intro j
    have hid := Real.pow_rpow_inv_natCast (hscalePos j).le
      hfourNe
    dsimp only
    convert hid using 1
    norm_num
  have hpMinusTwo : (fun ε : ℝ ↦ p ε - 2) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) := by
    have hthreeFive : (3 : ℕ) < 5 := by
      norm_num
    have hthreeFour : (3 : ℕ) < 4 := by
      norm_num
    have hfiveThree : (fun ε : ℝ ↦ ε ^ 5) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 3) :=
      (Asymptotics.isLittleO_pow_pow hthreeFive).isBigO
    have hfourThree : (fun ε : ℝ ↦ ε ^ 4) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 3) :=
      (Asymptotics.isLittleO_pow_pow hthreeFour).isBigO
    have hpoly : (fun ε : ℝ ↦
        (198 / 5 : ℝ) * ε ^ 3 - (9 / 5 : ℝ) * ε ^ 4) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 3) := by
      exact (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 3) (𝓝 0)).const_mul_left
          (198 / 5) |>.sub (hfourThree.const_mul_left (9 / 5))
    have hsum := h_pJet.trans hfiveThree |>.add hpoly
    refine hsum.congr_left ?_
    intro ε
    ring
  have hqZero : Tendsto (fun j : ℕ ↦ (orbit.state j).p - 2)
      atTop (𝓝 0) := by
    have hpowThree : Tendsto (fun ε : ℝ ↦ ε ^ 3) (𝓝 0) (𝓝 0) := by
      have hc : ContinuousAt (fun ε : ℝ ↦ ε ^ 3) 0 := by
        fun_prop
      simpa using hc.tendsto
    have hqRaw := hpMinusTwo.trans_tendsto hpowThree
    have hqSeq := hqRaw.comp hscaleZero
    refine hqSeq.congr' (Eventually.of_forall ?_)
    intro j
    simp only [Function.comp_apply]
    have hc := congrArg (fun z : ℝ × ℝ × ℝ ↦ z.2.1)
      (hgraphCoordinates j)
    simpa only [State.coordinates_def] using congrArg (fun x : ℝ ↦ x - 2) hc.symm
  intro Clim hClim
  have hεnonneg : ∀ᶠ j : ℕ in atTop, 0 ≤ (orbit.state j).ε :=
    Eventually.of_forall (fun j ↦ (hvalid j).ε_pos.le)
  have hampLowerEvent : ∀ᶠ j : ℕ in atTop,
      Gmin ≤ (orbit.state j).amplitude :=
    Eventually.of_forall hampLower
  have hcubeTarget := cube_isLittleO_amplitude_square
    hscaleZero hεnonneg hampLowerEvent hGmin
  have hcenterBigO :
      (fun j : ℕ ↦ (orbit.state j).center - Clim) =O[atTop]
        (fun j : ℕ ↦ (orbit.state j).ε ^ 3) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨Kcenter, Eventually.of_forall ?_⟩
    intro j
    have hbound :
        ‖(orbit.state j).center - Clim‖ +
            ‖(orbit.state j).middleCenter - Clim‖ ≤
          Kcenter * (orbit.state j).ε ^ 3 := by
      simpa only [orbit] using hCenter ε₀ hε₀Center Clim hClim j
    calc
      ‖(orbit.state j).center - Clim‖ ≤
          ‖(orbit.state j).center - Clim‖ +
            ‖(orbit.state j).middleCenter - Clim‖ :=
        le_add_of_nonneg_right (norm_nonneg _)
      _ ≤ Kcenter * (orbit.state j).ε ^ 3 := hbound
      _ = Kcenter * ‖(orbit.state j).ε ^ 3‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hvalid j).ε_pos.le 3)]
  have hcenterLittle :
      (fun j : ℕ ↦ (orbit.state j).center - Clim) =o[atTop]
        (fun j : ℕ ↦ (orbit.state j).amplitude * (orbit.state j).ε ^ 2) :=
    hcenterBigO.trans_isLittleO hcubeTarget
  have hqLittleOne :
      (fun j : ℕ ↦ (orbit.state j).p - 2) =o[atTop]
        (fun _j : ℕ ↦ (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 hqZero
  have hqAbsLittle :
      (fun j : ℕ ↦ |(orbit.state j).p - 2|) =o[atTop]
        (fun _j : ℕ ↦ (1 : ℝ)) := hqLittleOne.abs_left
  have hradialScalar := hqAbsLittle.mul_isBigO
    (Asymptotics.isBigO_refl
      (fun j : ℕ ↦ (orbit.state j).amplitude * (orbit.state j).ε ^ 2) atTop)
  have hradialScalar' :
      (fun j : ℕ ↦
        (orbit.state j).amplitude * |(orbit.state j).p - 2| *
          (orbit.state j).ε ^ 2) =o[atTop]
        (fun j : ℕ ↦ (orbit.state j).amplitude * (orbit.state j).ε ^ 2) := by
    have hleft : ∀ j : ℕ,
        |(orbit.state j).p - 2| *
            ((orbit.state j).amplitude * (orbit.state j).ε ^ 2) =
          (orbit.state j).amplitude * |(orbit.state j).p - 2| *
            (orbit.state j).ε ^ 2 := by
      intro j
      ring
    have hright : ∀ j : ℕ,
        (1 : ℝ) * ((orbit.state j).amplitude * (orbit.state j).ε ^ 2) =
          (orbit.state j).amplitude * (orbit.state j).ε ^ 2 := by
      intro j
      simp
    exact hradialScalar.congr' (Eventually.of_forall hleft)
      (Eventually.of_forall hright)
  have hradialNorm :
      (fun j : ℕ ↦
        ‖(orbit.state j).point - (orbit.state j).center -
          (orbit.state j).amplitude • WithLp.toLp 2
            ((orbit.state j).frame *ᵥ ![(1 : ℝ),
              2 * (orbit.state j).ε ^ 2])‖) =o[atTop]
        (fun j : ℕ ↦ (orbit.state j).amplitude * (orbit.state j).ε ^ 2) := by
    refine hradialScalar'.congr_left ?_
    intro j
    calc
      (orbit.state j).amplitude * |(orbit.state j).p - 2| *
          (orbit.state j).ε ^ 2 =
          ‖(orbit.state j).gradient -
          (orbit.state j).amplitude • WithLp.toLp 2
            ((orbit.state j).frame *ᵥ ![(1 : ℝ),
              2 * (orbit.state j).ε ^ 2])‖ := by
            exact (gradient_modelError_norm (orbit.state j) (hvalid j)).symm
      _ = ‖(orbit.state j).point - (orbit.state j).center -
          (orbit.state j).amplitude • WithLp.toLp 2
            ((orbit.state j).frame *ᵥ ![(1 : ℝ),
              2 * (orbit.state j).ε ^ 2])‖ := by
            rw [State.center_def]
            congr 1
            abel
  have hradial :
      (fun j : ℕ ↦
        (orbit.state j).point - (orbit.state j).center -
          (orbit.state j).amplitude • WithLp.toLp 2
            ((orbit.state j).frame *ᵥ ![(1 : ℝ),
              2 * (orbit.state j).ε ^ 2])) =o[atTop]
        (fun j : ℕ ↦ (orbit.state j).amplitude * (orbit.state j).ε ^ 2) :=
    hradialNorm.of_norm_left
  exact vectorExpansion_of_center_and_radialRemainders hcenterLittle hradial

end DFP.TwoPhaseOrbit
