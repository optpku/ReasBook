module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradient
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterDisplacement
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientLimit
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterTailUniform

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

/-- Every endpoint of a sufficiently small slow-curve orbit avoids each limiting center. -/
theorem slowCurveEndpointSubCenterLimit_ne_zero (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ k : ℕ, orbit.endpoint k - Clim ≠ 0 := by
  obtain ⟨εbarGradient, hεbarGradient, gmin, hgmin, gmax, hgminmax,
      hGradient⟩ :=
    slowCurveEndpointGradientNormUniformBounds p h h_invariant h_pJet h_hJet
  obtain ⟨εbarCenter, hεbarCenter, Kcenter, hKcenter, hCenter⟩ :=
    slowCurveCenterTailUniformBound p h h_invariant h_pJet h_hJet
  obtain ⟨εbarGraph, hεbarGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  have hden : 0 < 2 * (Kcenter + 1) := by positivity
  have hfrac : 0 < gmin / (2 * (Kcenter + 1)) := div_pos hgmin hden
  let δ : ℝ := min (1 / 4) (gmin / (2 * (Kcenter + 1)))
  let εbar : ℝ := min εbarGradient (min εbarCenter (min εbarGraph δ))
  have hδpos : 0 < δ := by
    dsimp only [δ]
    exact lt_min (by norm_num) hfrac
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hεbarGradient.1 (lt_min hεbarCenter.1 (lt_min hεbarGraph.1 hδpos))
  have hεbarLt : εbar < 1 / 4 := by
    exact (min_le_left _ _).trans_lt hεbarGradient.2
  have hKeps_lt (ε₀ : ℝ) (hε₀ : ε₀ ∈ Set.Ioc 0 εbar) :
      Kcenter * ε₀ ^ 3 < gmin := by
    have hεδ : ε₀ ≤ δ := by
      exact hε₀.2.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
    have hεnonneg : 0 ≤ ε₀ := hε₀.1.le
    have hεone : ε₀ ≤ 1 := by
      have hδle : δ ≤ 1 / 4 := by
        dsimp only [δ]
        exact min_le_left _ _
      linarith
    have hpow : ε₀ ^ 3 ≤ ε₀ := by
      exact pow_le_of_le_one hεnonneg hεone (by norm_num)
    have hεfrac : ε₀ ≤ gmin / (2 * (Kcenter + 1)) := by
      exact hεδ.trans (by
        dsimp only [δ]
        exact min_le_right _ _)
    have hmul : Kcenter * ε₀ ≤
        Kcenter * (gmin / (2 * (Kcenter + 1))) :=
      mul_le_mul_of_nonneg_left hεfrac hKcenter.le
    have hfracLt : Kcenter * (gmin / (2 * (Kcenter + 1))) < gmin := by
      rw [show Kcenter * (gmin / (2 * (Kcenter + 1))) =
        (Kcenter * gmin) / (2 * (Kcenter + 1)) by ring]
      apply (div_lt_iff₀ hden).2
      nlinarith
    exact (mul_le_mul_of_nonneg_left hpow hKcenter.le).trans_lt
      (hmul.trans_lt hfracLt)
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Gradient : ε₀ ∈ Set.Ioc 0 εbarGradient := by
    exact ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hε₀Center : ε₀ ∈ Set.Ioc 0 εbarCenter := by
    exact ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 εbarGraph := by
    exact ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))⟩
  intro Clim hClim k
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · intro hzero
    have hzero' : orbit.endpoint (2 * j) - Clim = 0 := by
      simpa only [orbit] using hzero
    have hgradientMem : ‖orbit.endpointGradient (2 * j)‖ ∈ Set.Icc gmin gmax := by
      simpa only [orbit] using hGradient ε₀ hε₀Gradient (2 * j)
    have htail : ‖(orbit.state j).center - Clim‖ +
        ‖(orbit.state j).middleCenter - Clim‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 := by
      simpa only [orbit] using hCenter ε₀ hε₀Center Clim hClim j
    have hcenter : ‖(orbit.state j).center - Clim‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 :=
      (le_add_of_nonneg_right (norm_nonneg _)).trans htail
    have hdecomp : (orbit.state j).gradient =
        (orbit.endpoint (2 * j) - Clim) -
          ((orbit.state j).center - Clim) := by
      rw [endpoint_even, State.center_def]
      abel
    have hgradientBound : ‖(orbit.state j).gradient‖ ≤
        ‖orbit.endpoint (2 * j) - Clim‖ +
          ‖(orbit.state j).center - Clim‖ := by
      rw [hdecomp]
      exact norm_sub_le _ _
    have hgradientSmall : ‖(orbit.state j).gradient‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 := by
      calc
        ‖(orbit.state j).gradient‖ ≤
            ‖orbit.endpoint (2 * j) - Clim‖ +
              ‖(orbit.state j).center - Clim‖ := hgradientBound
        _ = ‖(orbit.state j).center - Clim‖ := by simp [hzero']
        _ ≤ Kcenter * (orbit.state j).ε ^ 3 := hcenter
    have hgradientLower : gmin ≤ ‖(orbit.state j).gradient‖ := by
      simpa only [endpointGradient_even] using hgradientMem.1
    exact (not_lt_of_ge hgradientLower)
      ((hgradientSmall.trans (by
        have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
        have hcoord' : (orbit.state j).coordinates =
            DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
          simpa only [orbit] using hcoord
        have hεeq : (orbit.state j).ε =
            (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
          simpa only [State.coordinates_def] using congrArg Prod.fst hcoord'
        have hforward := hGraph ε₀ hε₀Graph j
        have hforward' :
            (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 ∈
              Set.Ioc 0 ε₀ := by
          simpa only using hforward.2
        have hεstate : (orbit.state j).ε ≤ ε₀ := by
          rw [hεeq]
          exact hforward'.2
        have hεstatePos : 0 ≤ (orbit.state j).ε := by
          rw [hεeq]
          exact hforward'.1.le
        have hpowState : (orbit.state j).ε ^ 3 ≤ ε₀ ^ 3 :=
          pow_le_pow_left₀ hεstatePos hεstate 3
        exact mul_le_mul_of_nonneg_left hpowState hKcenter.le)).trans_lt
        (hKeps_lt ε₀ hε₀))
  · intro hzero
    have hzero' : orbit.endpoint (2 * j + 1) - Clim = 0 := by
      simpa only [orbit] using hzero
    have hgradientMem : ‖orbit.endpointGradient (2 * j + 1)‖ ∈ Set.Icc gmin gmax := by
      simpa only [orbit] using hGradient ε₀ hε₀Gradient (2 * j + 1)
    have htail : ‖(orbit.state j).center - Clim‖ +
        ‖(orbit.state j).middleCenter - Clim‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 := by
      simpa only [orbit] using hCenter ε₀ hε₀Center Clim hClim j
    have hmiddle : ‖(orbit.state j).middleCenter - Clim‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 :=
      (le_add_of_nonneg_left (norm_nonneg _)).trans htail
    have hdecomp : (orbit.state j).middleGradient =
        (orbit.endpoint (2 * j + 1) - Clim) -
          ((orbit.state j).middleCenter - Clim) := by
      rw [endpoint_odd, State.middleCenter_def]
      abel
    have hgradientBound : ‖(orbit.state j).middleGradient‖ ≤
        ‖orbit.endpoint (2 * j + 1) - Clim‖ +
          ‖(orbit.state j).middleCenter - Clim‖ := by
      rw [hdecomp]
      exact norm_sub_le _ _
    have hgradientSmall : ‖(orbit.state j).middleGradient‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 := by
      calc
        ‖(orbit.state j).middleGradient‖ ≤
            ‖orbit.endpoint (2 * j + 1) - Clim‖ +
              ‖(orbit.state j).middleCenter - Clim‖ := hgradientBound
        _ = ‖(orbit.state j).middleCenter - Clim‖ := by simp [hzero']
        _ ≤ Kcenter * (orbit.state j).ε ^ 3 := hmiddle
    have hgradientLower : gmin ≤ ‖(orbit.state j).middleGradient‖ := by
      simpa only [endpointGradient_odd] using hgradientMem.1
    exact (not_lt_of_ge hgradientLower)
      ((hgradientSmall.trans (by
        have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
        have hcoord' : (orbit.state j).coordinates =
            DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
          simpa only [orbit] using hcoord
        have hεeq : (orbit.state j).ε =
            (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
          simpa only [State.coordinates_def] using congrArg Prod.fst hcoord'
        have hforward := hGraph ε₀ hε₀Graph j
        have hforward' :
            (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 ∈
              Set.Ioc 0 ε₀ := by
          simpa only using hforward.2
        have hεstate : (orbit.state j).ε ≤ ε₀ := by
          rw [hεeq]
          exact hforward'.2
        have hεstatePos : 0 ≤ (orbit.state j).ε := by
          rw [hεeq]
          exact hforward'.1.le
        have hpowState : (orbit.state j).ε ^ 3 ≤ ε₀ ^ 3 :=
          pow_le_pow_left₀ hεstatePos hεstate 3
        exact mul_le_mul_of_nonneg_left hpowState hKcenter.le)).trans_lt
        (hKeps_lt ε₀ hε₀))

end DFP.TwoPhaseOrbit
