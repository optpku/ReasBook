module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterTailUniform
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradient
public import ReasLib.Optimization.DFP.TwoPhaseControls

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

/-- The center `x_k - g_k` attached to flattened endpoint `k`. -/
def endpointCenter (orbit : DFP.TwoPhaseOrbit) (k : ℕ) :
    EuclideanSpace ℝ (Fin 2) :=
  orbit.endpoint k - orbit.endpointGradient k

/-- The endpoint center is the endpoint minus its prescribed gradient. -/
theorem endpointCenter_def (orbit : DFP.TwoPhaseOrbit) (k : ℕ) :
    orbit.endpointCenter k = orbit.endpoint k - orbit.endpointGradient k := by
  rw [endpointCenter]

/-- At an even endpoint, `endpointCenter` is the corresponding cycle-boundary center. -/
theorem endpointCenter_even (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpointCenter (2 * j) = (orbit.state j).center := by
  rw [endpointCenter, endpoint_even, endpointGradient_even, State.center_def]

/-- At an odd endpoint, `endpointCenter` is the corresponding intermediate center. -/
theorem endpointCenter_odd (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpointCenter (2 * j + 1) = (orbit.state j).middleCenter := by
  rw [endpointCenter, endpoint_odd, endpointGradient_odd, State.middleCenter_def]

/-- The correction vector `g_k - (x_k - C)` at flattened endpoint `k`. -/
def endpointCorrection (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  orbit.endpointGradient k - (orbit.endpoint k - C)

/-- The endpoint correction is the prescribed gradient minus the translated
endpoint. -/
theorem endpointCorrection_def (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) :
    orbit.endpointCorrection C k =
      orbit.endpointGradient k - (orbit.endpoint k - C) := by
  rw [endpointCorrection]

/-- The endpoint correction is the limiting center minus the endpoint center. -/
theorem endpointCorrection_eq_center (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) :
    orbit.endpointCorrection C k = C - orbit.endpointCenter k := by
  rw [endpointCorrection, endpointCenter]
  abel

/-- At an even endpoint, the correction is the limiting center minus the boundary center. -/
theorem endpointCorrection_even (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ) :
    orbit.endpointCorrection C (2 * j) = C - (orbit.state j).center := by
  rw [endpointCorrection_eq_center, endpointCenter_even]

/-- At an odd endpoint, the correction is the limiting center minus the intermediate center. -/
theorem endpointCorrection_odd (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ) :
    orbit.endpointCorrection C (2 * j + 1) = C - (orbit.state j).middleCenter := by
  rw [endpointCorrection_eq_center, endpointCenter_odd]

/-- The squared cycle scale `r(k)` attached to flattened endpoint `k`. -/
def endpointRadius (orbit : DFP.TwoPhaseOrbit) (k : ℕ) : ℝ :=
  TwoPhaseControls.radius (orbit.state (k / 2)).ε

/-- The endpoint radius is the square of its cycle scale. -/
theorem endpointRadius_def (orbit : DFP.TwoPhaseOrbit) (k : ℕ) :
    orbit.endpointRadius k = (orbit.state (k / 2)).ε ^ 2 := by
  rw [endpointRadius, TwoPhaseControls.radius_def]

/-- At an even endpoint, the radius is the square of the corresponding cycle scale. -/
theorem endpointRadius_even (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpointRadius (2 * j) = (orbit.state j).ε ^ 2 := by
  rw [endpointRadius_def]
  have hdiv : (2 * j) / 2 = j := by omega
  rw [hdiv]

/-- At an odd endpoint, the radius is the square of the corresponding cycle scale. -/
theorem endpointRadius_odd (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpointRadius (2 * j + 1) = (orbit.state j).ε ^ 2 := by
  rw [endpointRadius_def]
  have hdiv : (2 * j + 1) / 2 = j := by omega
  rw [hdiv]

/-- The cube of an endpoint's cycle scale is that scale times its endpoint radius. -/
theorem endpointScale_mul_radius (orbit : DFP.TwoPhaseOrbit) (k : ℕ) :
    (orbit.state (k / 2)).ε ^ 3 =
      (orbit.state (k / 2)).ε * orbit.endpointRadius k := by
  rw [endpointRadius_def]
  ring

/-- A single positive constant uniformly controls endpoint corrections by the cube of their cycle scale. -/
theorem slowCurveEndpointCorrectionUniformBound (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kcorrection > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ k : ℕ, ‖orbit.endpointCorrection Clim k‖ ≤
              Kcorrection * (orbit.state (k / 2)).ε ^ 3 := by
  obtain ⟨εbar, hεbar, Kcenter, hKcenter, hcenter⟩ :=
    slowCurveCenterTailUniformBound p h h_invariant h_pJet h_hJet
  refine ⟨εbar, hεbar, Kcenter, hKcenter, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  intro Clim hClim k
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [endpointCorrection_even]
    have hdiv : (2 * j) / 2 = j := by omega
    rw [hdiv]
    have htail : ‖(orbit.state j).center - Clim‖ +
        ‖(orbit.state j).middleCenter - Clim‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 := by
      simpa only [orbit] using hcenter ε₀ hε₀ Clim hClim j
    calc
      ‖Clim - (orbit.state j).center‖ =
          ‖(orbit.state j).center - Clim‖ := norm_sub_rev _ _
      _ ≤ ‖(orbit.state j).center - Clim‖ +
          ‖(orbit.state j).middleCenter - Clim‖ :=
        le_add_of_nonneg_right (norm_nonneg _)
      _ ≤ Kcenter * (orbit.state j).ε ^ 3 := htail
  · rw [endpointCorrection_odd]
    have hdiv : (2 * j + 1) / 2 = j := by omega
    rw [hdiv]
    have htail : ‖(orbit.state j).center - Clim‖ +
        ‖(orbit.state j).middleCenter - Clim‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 := by
      simpa only [orbit] using hcenter ε₀ hε₀ Clim hClim j
    calc
      ‖Clim - (orbit.state j).middleCenter‖ =
          ‖(orbit.state j).middleCenter - Clim‖ := norm_sub_rev _ _
      _ ≤ ‖(orbit.state j).center - Clim‖ +
          ‖(orbit.state j).middleCenter - Clim‖ :=
        le_add_of_nonneg_left (norm_nonneg _)
      _ ≤ Kcenter * (orbit.state j).ε ^ 3 := htail

/-- A single positive constant uniformly controls endpoint corrections by scale times endpoint radius. -/
theorem slowCurveEndpointCorrectionRadiusUniformBound (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kcorrection > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ k : ℕ, ‖orbit.endpointCorrection Clim k‖ ≤
              Kcorrection * (orbit.state (k / 2)).ε * orbit.endpointRadius k := by
  obtain ⟨εbar, hεbar, Kcorrection, hKcorrection, hbound⟩ :=
    slowCurveEndpointCorrectionUniformBound p h h_invariant h_pJet h_hJet
  refine ⟨εbar, hεbar, Kcorrection, hKcorrection, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  intro Clim hClim k
  have hcube := hbound ε₀ hε₀ Clim hClim k
  have hcube' : ‖orbit.endpointCorrection Clim k‖ ≤
      Kcorrection * (orbit.state (k / 2)).ε ^ 3 := by
    simpa only [orbit] using hcube
  calc
    ‖orbit.endpointCorrection Clim k‖ ≤
        Kcorrection * (orbit.state (k / 2)).ε ^ 3 := hcube'
    _ = Kcorrection * ((orbit.state (k / 2)).ε * orbit.endpointRadius k) := by
      rw [endpointScale_mul_radius]
    _ = Kcorrection * (orbit.state (k / 2)).ε * orbit.endpointRadius k := by
      ring

end DFP.TwoPhaseOrbit
