module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointIsolation.SupportDistance
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_5_3_Disjoint_endpoint_bump_corrections_Bump
import ReasLib.Analysis.Calculus.EuclideanPlaneSmoothCutoff

public section

noncomputable section

open Filter
open scoped Asymptotics Topology

/-- Lemma 5.6 (Support distance is comparable to the cycle scale) (1): eventually,
every point in the support of the `k`th endpoint bump has distance from the limiting
circle bounded above and below by positive multiples of the scale of cycle `k / 2`. -/
theorem slowCurveBumpSupportDistanceBounds (p h : ℝ → ℝ)
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
              ∃ cLower > 0, ∃ cUpper > 0,
                ∀ᶠ k : ℕ in atTop, ∀ z ∈ tsupport (orbit.endpointBump Clim Glim k),
                  Metric.infDist z (DFP.TwoPhaseOrbit.limitCircle Clim Glim) ∈ Set.Icc
                    (cLower * (orbit.state (k / 2)).ε)
                    (cUpper * (orbit.state (k / 2)).ε) := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  obtain ⟨ηSupport, hηSupport, hSupport⟩ := curve.supportInfDistUniformBounds
  obtain ⟨ηRadius, hηRadius, hRadiusPos⟩ := curve.interpolationRadius_pos
  let εbar := min ηSupport ηRadius
  have hεbarPos : 0 < εbar := lt_min hηSupport.1 hηRadius.1
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηSupport.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεSupport : ε₀ ∈ Set.Ioc 0 ηSupport :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεRadius : ε₀ ∈ Set.Ioc 0 ηRadius :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  intro Clim hClim Glim hGlim hGlimTendsto
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
  have hSupportData :=
    hSupport ε₀ hεSupport Clim hClim' Glim hGlim hGlimTendsto'
  have hRadiusData :=
    hRadiusPos ε₀ hεRadius Clim hClim' Glim hGlim hGlimTendsto'
  let support : ℕ → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun k ↦ tsupport (orbit.endpointBump Clim Glim k)
  have hSupportSubset (k : ℕ) : support k ⊆
      Metric.closedBall (orbit.endpoint k)
        (orbit.interpolationRadius Clim Glim k) := by
    dsimp only [support]
    rw [DFP.TwoPhaseOrbit.endpointBump_eq_scaledLinearBump]
    apply AffineBump.tsupport_scaledLinearBump_subset_closedBall
      EuclideanPlane.smoothCutoff EuclideanPlane.tsupport_smoothCutoff_subset
    simpa only [orbit, curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hRadiusData k
  have hSupportSubset' (k : ℕ) : support k ⊆
      Metric.closedBall
        ((DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).endpoint k)
        ((DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).interpolationRadius
          Clim Glim k) := by
    simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high, orbit] using hSupportSubset k
  simpa only [support, orbit, curve,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using
      hSupportData support hSupportSubset'

/-- The quadratic-radius assertion of Lemma 5.6 (Support distance is comparable to the
cycle scale): the interpolation radius is eventually bounded by a constant multiple of
the squared scale of its cycle. -/
theorem slowCurveInterpolationRadiusIsBigO (p h : ℝ → ℝ)
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
              (fun k : ℕ ↦ orbit.interpolationRadius Clim Glim k) =O[atTop]
                (fun k : ℕ ↦ (orbit.state (k / 2)).ε ^ 2) := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, hCore⟩ := curve.interpolationRadius_isBigO_endpointRadius
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  intro Clim hClim Glim hGlim hGlimTendsto
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
  have hBig := hCore ε₀ hε₀ Clim hClim' Glim hGlim hGlimTendsto'
  have hBig' : (fun k : ℕ ↦ orbit.interpolationRadius Clim Glim k) =O[atTop]
      orbit.endpointRadius := by
    simpa only [orbit, curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hBig
  refine hBig'.congr' Filter.EventuallyEq.rfl (Eventually.of_forall ?_)
  intro k
  exact DFP.TwoPhaseOrbit.endpointRadius_def orbit k
