module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_5_3_Disjoint_endpoint_bump_corrections_Bump
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBumpBounds

public section

noncomputable section

open Filter Set
open scoped ContDiff Topology

/-- Lemma 5.5 (Uniform supportwise value, gradient, and Hessian bounds) (1):
uniformly over sufficiently small initial scales, the value of each endpoint bump on
its support is bounded by a constant times the cycle scale and the square of the
endpoint radius. -/
theorem slowCurveBumpValueUniformBound (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∃ Kvalue > 0,
      ∀ ε₀ ∈ Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ k : ℕ, ∀ z : EuclideanSpace ℝ (Fin 2),
                  z ∈ tsupport (orbit.endpointBump Clim Glim k) →
                    ‖orbit.endpointBump Clim Glim k z‖ ≤
                      Kvalue * (orbit.state (k / 2)).ε *
                        orbit.endpointRadius k ^ 2 := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, Kvalue, hKvalue, Kgradient, hKgradient,
      Khessian, hKhessian, hcore⟩ :=
    DFP.TwoLeg.SlowCurve.endpointBumpUniformBounds curve
  have hcore' := hcore
  simp only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] at hcore'
  refine ⟨εbar, hεbar, Kvalue, hKvalue, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro Clim hClim Glim hGlim hGlimTendsto k z hz
  exact (hcore' ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto k z hz).1

/-- Lemma 5.5 (Uniform supportwise value, gradient, and Hessian bounds) (2):
uniformly over sufficiently small initial scales, the norm of the first Fréchet
derivative (the source gradient) of each endpoint bump on its support is bounded by a
constant times the cycle scale and the endpoint radius. -/
theorem slowCurveBumpFDerivUniformBound (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∃ Kgradient > 0,
      ∀ ε₀ ∈ Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ k : ℕ, ∀ z : EuclideanSpace ℝ (Fin 2),
                  z ∈ tsupport (orbit.endpointBump Clim Glim k) →
                    ‖fderiv ℝ (orbit.endpointBump Clim Glim k) z‖ ≤
                      Kgradient * (orbit.state (k / 2)).ε *
                        orbit.endpointRadius k := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, Kvalue, hKvalue, Kgradient, hKgradient,
      Khessian, hKhessian, hcore⟩ :=
    DFP.TwoLeg.SlowCurve.endpointBumpUniformBounds curve
  have hcore' := hcore
  simp only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] at hcore'
  refine ⟨εbar, hεbar, Kgradient, hKgradient, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro Clim hClim Glim hGlim hGlimTendsto k z hz
  exact (hcore' ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto k z hz).2.1

/-- Lemma 5.5 (Uniform supportwise value, gradient, and Hessian bounds) (3):
uniformly over sufficiently small initial scales, the norm of the second Fréchet
derivative (the source Hessian) of each endpoint bump on its support is bounded by a
constant times the cycle scale. -/
theorem slowCurveBumpSecondFDerivUniformBound (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∃ Khessian > 0,
      ∀ ε₀ ∈ Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ k : ℕ, ∀ z : EuclideanSpace ℝ (Fin 2),
                  z ∈ tsupport (orbit.endpointBump Clim Glim k) →
                    ‖fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) z‖ ≤
                      Khessian * (orbit.state (k / 2)).ε := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, Kvalue, hKvalue, Kgradient, hKgradient,
      Khessian, hKhessian, hcore⟩ :=
    DFP.TwoLeg.SlowCurve.endpointBumpUniformBounds curve
  have hcore' := hcore
  simp only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] at hcore'
  refine ⟨εbar, hεbar, Khessian, hKhessian, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro Clim hClim Glim hGlim hGlimTendsto k z hz
  exact (hcore' ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto k z hz).2.2
