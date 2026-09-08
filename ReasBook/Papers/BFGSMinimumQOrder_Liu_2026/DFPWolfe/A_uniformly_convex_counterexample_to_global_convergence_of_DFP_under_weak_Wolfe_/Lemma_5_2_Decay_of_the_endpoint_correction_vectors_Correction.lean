module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointCorrection

public section

open Filter
open scoped Topology

#check (DFP.TwoPhaseOrbit.endpointCenter :
  DFP.TwoPhaseOrbit → ℕ → EuclideanSpace ℝ (Fin 2))

#check (DFP.TwoPhaseOrbit.endpointCenter_even :
  ∀ (orbit : DFP.TwoPhaseOrbit) (j : ℕ),
    orbit.endpointCenter (2 * j) = (orbit.state j).center)

#check (DFP.TwoPhaseOrbit.endpointCenter_odd :
  ∀ (orbit : DFP.TwoPhaseOrbit) (j : ℕ),
    orbit.endpointCenter (2 * j + 1) = (orbit.state j).middleCenter)

#check (DFP.TwoPhaseOrbit.endpointCorrection :
  DFP.TwoPhaseOrbit → EuclideanSpace ℝ (Fin 2) → ℕ →
    EuclideanSpace ℝ (Fin 2))

#check (DFP.TwoPhaseOrbit.endpointCorrection_eq_center :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ),
    orbit.endpointCorrection C k = C - orbit.endpointCenter k)

#check (DFP.TwoPhaseOrbit.endpointCorrection_even :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ),
    orbit.endpointCorrection C (2 * j) = C - (orbit.state j).center)

#check (DFP.TwoPhaseOrbit.endpointCorrection_odd :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ),
    orbit.endpointCorrection C (2 * j + 1) = C - (orbit.state j).middleCenter)

#check (DFP.TwoPhaseOrbit.endpointRadius :
  DFP.TwoPhaseOrbit → ℕ → ℝ)

#check (DFP.TwoPhaseOrbit.endpointRadius_def :
  ∀ (orbit : DFP.TwoPhaseOrbit) (k : ℕ),
    orbit.endpointRadius k = (orbit.state (k / 2)).ε ^ 2)

#check (DFP.TwoPhaseOrbit.endpointRadius_even :
  ∀ (orbit : DFP.TwoPhaseOrbit) (j : ℕ),
    orbit.endpointRadius (2 * j) = (orbit.state j).ε ^ 2)

#check (DFP.TwoPhaseOrbit.endpointRadius_odd :
  ∀ (orbit : DFP.TwoPhaseOrbit) (j : ℕ),
    orbit.endpointRadius (2 * j + 1) = (orbit.state j).ε ^ 2)

#check (DFP.TwoPhaseOrbit.endpointScale_mul_radius :
  ∀ (orbit : DFP.TwoPhaseOrbit) (k : ℕ),
    (orbit.state (k / 2)).ε ^ 3 =
      (orbit.state (k / 2)).ε * orbit.endpointRadius k)

#check (DFP.TwoPhaseOrbit.slowCurveEndpointCorrectionUniformBound :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kcorrection > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ k : ℕ, ‖orbit.endpointCorrection Clim k‖ ≤
              Kcorrection * (orbit.state (k / 2)).ε ^ 3)

#check (DFP.TwoPhaseOrbit.slowCurveEndpointCorrectionRadiusUniformBound :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Kcorrection > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ k : ℕ, ‖orbit.endpointCorrection Clim k‖ ≤
              Kcorrection * (orbit.state (k / 2)).ε * orbit.endpointRadius k)
