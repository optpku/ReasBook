module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump.JetDecay

public section

noncomputable section

open Filter Set
open scoped Asymptotics Topology

/- Lemma 5.7 (Vanishing second-order jets at the limiting circle): the
normalized endpoint-bump value and first derivative, together with the second
derivative, vanish simultaneously along supports approaching the circle. -/
#check DFP.TwoLeg.SlowCurve.endpointBumpSecondOrderJetsVanish

/-- Lemma 5.7 (Vanishing second-order jets at the limiting circle) (4): the endpoint
bump value divided by squared distance to the limiting circle tends uniformly to zero
along support points approaching that circle. -/
theorem slowCurveBumpValueDistSqDecay (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ η > 0, ∃ δ > 0, ∀ k : ℕ, ∀ z : EuclideanSpace ℝ (Fin 2),
                z ∈ (DFP.TwoPhaseOrbit.limitCircle Clim Glim)ᶜ →
                  z ∈ tsupport (orbit.endpointBump Clim Glim k) →
                    Metric.infDist z (DFP.TwoPhaseOrbit.limitCircle Clim Glim) < δ →
                      ‖orbit.endpointBump Clim Glim k z‖ /
                          Metric.infDist z
                            (DFP.TwoPhaseOrbit.limitCircle Clim Glim) ^ 2 < η := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, hVanish⟩ :=
    curve.endpointBumpSecondOrderJetsVanish
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  let curveOrbit :=
    DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  intro Clim hClim Glim hGlim hGlimTendsto η hη
  have hClimCurve : Tendsto
      (fun j : ℕ ↦ (curveOrbit.state j).center) atTop (𝓝 Clim) := by
    simpa only [curveOrbit, orbit, curve,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hClim
  have hGlimCurve : Tendsto
      (fun j : ℕ ↦ (curveOrbit.state j).amplitude) atTop (𝓝 Glim) := by
    simpa only [curveOrbit, orbit, curve,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hGlimTendsto
  obtain ⟨δ, hδ, hDecay⟩ :=
    hVanish ε₀ hε₀ Clim hClimCurve Glim hGlim hGlimCurve η hη
  refine ⟨δ, hδ, ?_⟩
  intro k z _ hz hzδ
  have hzCurve :
      z ∈ tsupport (curveOrbit.endpointBump Clim Glim k) := by
    simpa only [curveOrbit, orbit, curve,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hz
  have hJet := hDecay k z hzCurve hzδ
  simpa only [curveOrbit, orbit, curve,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hJet.1

/-- Lemma 5.7 (Vanishing second-order jets at the limiting circle) (5): the norm of
the first Fréchet derivative divided by distance to the limiting circle tends uniformly
to zero along support points approaching that circle. -/
theorem slowCurveBumpFDerivDistDecay (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ η > 0, ∃ δ > 0, ∀ k : ℕ, ∀ z : EuclideanSpace ℝ (Fin 2),
                z ∈ (DFP.TwoPhaseOrbit.limitCircle Clim Glim)ᶜ →
                  z ∈ tsupport (orbit.endpointBump Clim Glim k) →
                    Metric.infDist z (DFP.TwoPhaseOrbit.limitCircle Clim Glim) < δ →
                      ‖fderiv ℝ (orbit.endpointBump Clim Glim k) z‖ /
                          Metric.infDist z
                            (DFP.TwoPhaseOrbit.limitCircle Clim Glim) < η := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, hVanish⟩ :=
    curve.endpointBumpSecondOrderJetsVanish
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  let curveOrbit :=
    DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  intro Clim hClim Glim hGlim hGlimTendsto η hη
  have hClimCurve : Tendsto
      (fun j : ℕ ↦ (curveOrbit.state j).center) atTop (𝓝 Clim) := by
    simpa only [curveOrbit, orbit, curve,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hClim
  have hGlimCurve : Tendsto
      (fun j : ℕ ↦ (curveOrbit.state j).amplitude) atTop (𝓝 Glim) := by
    simpa only [curveOrbit, orbit, curve,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hGlimTendsto
  obtain ⟨δ, hδ, hDecay⟩ :=
    hVanish ε₀ hε₀ Clim hClimCurve Glim hGlim hGlimCurve η hη
  refine ⟨δ, hδ, ?_⟩
  intro k z _ hz hzδ
  have hzCurve :
      z ∈ tsupport (curveOrbit.endpointBump Clim Glim k) := by
    simpa only [curveOrbit, orbit, curve,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hz
  have hJet := hDecay k z hzCurve hzδ
  simpa only [curveOrbit, orbit, curve,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hJet.2.1

/-- Lemma 5.7 (Vanishing second-order jets at the limiting circle) (6): the norm of
the second Fréchet derivative tends uniformly to zero along support points approaching
the limiting circle. -/
theorem slowCurveBumpSecondFDerivDecay (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ η > 0, ∃ δ > 0, ∀ k : ℕ, ∀ z : EuclideanSpace ℝ (Fin 2),
                z ∈ (DFP.TwoPhaseOrbit.limitCircle Clim Glim)ᶜ →
                  z ∈ tsupport (orbit.endpointBump Clim Glim k) →
                    Metric.infDist z (DFP.TwoPhaseOrbit.limitCircle Clim Glim) < δ →
                      ‖fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) z‖ < η := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, hVanish⟩ :=
    curve.endpointBumpSecondOrderJetsVanish
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  let curveOrbit :=
    DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  intro Clim hClim Glim hGlim hGlimTendsto η hη
  have hClimCurve : Tendsto
      (fun j : ℕ ↦ (curveOrbit.state j).center) atTop (𝓝 Clim) := by
    simpa only [curveOrbit, orbit, curve,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hClim
  have hGlimCurve : Tendsto
      (fun j : ℕ ↦ (curveOrbit.state j).amplitude) atTop (𝓝 Glim) := by
    simpa only [curveOrbit, orbit, curve,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hGlimTendsto
  obtain ⟨δ, hδ, hDecay⟩ :=
    hVanish ε₀ hε₀ Clim hClimCurve Glim hGlim hGlimCurve η hη
  refine ⟨δ, hδ, ?_⟩
  intro k z _ hz hzδ
  have hzCurve :
      z ∈ tsupport (curveOrbit.endpointBump Clim Glim k) := by
    simpa only [curveOrbit, orbit, curve,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hz
  have hJet := hDecay k z hzCurve hzδ
  simpa only [curveOrbit, orbit, curve,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hJet.2.2
