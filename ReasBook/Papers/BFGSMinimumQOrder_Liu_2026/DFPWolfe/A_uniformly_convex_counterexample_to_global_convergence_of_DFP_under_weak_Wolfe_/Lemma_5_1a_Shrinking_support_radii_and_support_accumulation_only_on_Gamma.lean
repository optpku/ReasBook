module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointIsolation.ShrinkingSupport
public import DFPWolfe.Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample.Infrastructure_I_26_Derivative_formulas_and_scale_bounds_for_affine_cutoff_bumps_AffineBump

public section

noncomputable section

open Filter
open scoped Asymptotics Topology

/-- Lemma 5.1a (Shrinking support radii and support accumulation only on $\Gamma$) (1):
uniformly over sufficiently small slow-curve orbits, the interpolation radii tend to
zero. -/
theorem slowCurveInterpolationRadiusTendstoZero (p h : ℝ → ℝ)
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
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              Tendsto (fun k : ℕ ↦ orbit.interpolationRadius Clim Glim k)
                atTop (𝓝 0) := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using
      curve.interpolationRadiusTendstoZero

/- Lemma 5.1a (Shrinking support radii and support accumulation only on $\Gamma$) (2):
the bundled library theorem says that every `atTop` endpoint cluster point lies
on the limiting circle. -/
#check DFP.TwoLeg.SlowCurve.endpointClusterPt_mem_limitCircle

/-- Every affine-cutoff support lies in the closed interpolation ball centered at the
corresponding endpoint, uniformly over sufficiently small slow-curve orbits. This is
conclusion (3) of Lemma 5.1a (Shrinking support radii and support accumulation only on
$\Gamma$). -/
theorem slowCurveAffineCutoffBumpSupportSubsetInterpolationClosedBall
    (p h : ℝ → ℝ) (χ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (a : ℕ → EuclideanSpace ℝ (Fin 2))
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))
    (hχ_support : tsupport χ ⊆ Metric.ball 0 1) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ k : ℕ, tsupport
                (affineCutoffBump χ (orbit.endpoint k)
                  (orbit.interpolationRadius Clim Glim k) (a k)) ⊆
                Metric.closedBall (orbit.endpoint k)
                  (orbit.interpolationRadius Clim Glim k) := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, hRadiusPos⟩ := curve.interpolationRadius_pos
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro Clim hClim Glim hGlim hGlimTendsto k
  have hClim' : Tendsto
      (fun j : ℕ ↦
        ((DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).state j).center)
      atTop (nhds Clim) := by
    simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hClim
  have hGlimTendsto' : Tendsto
      (fun j : ℕ ↦
        ((DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).state j).amplitude)
      atTop (nhds Glim) := by
    simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hGlimTendsto
  have hρ : 0 < (DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).interpolationRadius
      Clim Glim k := by
    simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using
        hRadiusPos ε₀ hε₀ Clim hClim' Glim hGlim hGlimTendsto' k
  change tsupport (AffineBump.scaledLinearBump χ
      ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).endpoint k)
      ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).interpolationRadius Clim Glim k)
      (a k)) ⊆
    Metric.closedBall ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).endpoint k)
      ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).interpolationRadius Clim Glim k)
  exact AffineBump.tsupport_scaledLinearBump_subset_closedBall
    χ hχ_support _ _ _ hρ

/-- Every positive closed thickening of the limiting circle eventually contains every
interpolation ball, uniformly over sufficiently small slow-curve orbits. This is
conclusion (4) of Lemma 5.1a (Shrinking support radii and support accumulation only on
$\Gamma$). -/
theorem slowCurveInterpolationBallsEventuallyNearLimitCircle (p h : ℝ → ℝ)
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
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ δ > 0, ∀ᶠ k : ℕ in atTop,
                Metric.closedBall (orbit.endpoint k)
                    (orbit.interpolationRadius Clim Glim k) ⊆
                  Metric.cthickening δ (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using
      curve.interpolationBallsEventuallyNearLimitCircle
