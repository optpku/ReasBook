module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointIsolation.SlowCurve

public section

open Filter
open scoped Topology

/-- Lemma 5.1 (Isolation radii and pairwise-disjoint interpolation balls) (1):
uniformly over sufficiently small initial scales, every interpolation radius is bounded
above and below by positive multiples of the squared scale of its cycle. -/
theorem slowCurveInterpolationRadiusUniformBounds (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cLower > 0, ∃ cUpper > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ k : ℕ, orbit.interpolationRadius Clim Glim k ∈ Set.Icc
                  (cLower * (orbit.state (k / 2)).ε ^ 2)
                  (cUpper * (orbit.state (k / 2)).ε ^ 2) := by
  let curve :=
    DFP.TwoLeg.SlowCurve.ofAsymptotics p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, cLower, hcLower, cUpper, hcUpper, hBounds⟩ :=
    DFP.TwoLeg.SlowCurve.interpolationRadiusUniformBounds curve
  have hBounds' := hBounds
  simp only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] at hBounds'
  refine ⟨εbar, hεbar, cLower, hcLower, cUpper, hcUpper, ?_⟩
  intro ε₀ hε₀
  simpa only [DFP.TwoPhaseOrbit.endpointRadius_def] using hBounds' ε₀ hε₀

/-- Lemma 5.1 (Isolation radii and pairwise-disjoint interpolation balls) (2):
uniformly over sufficiently small initial scales, the closed interpolation balls are
pairwise disjoint. -/
theorem slowCurvePairwiseDisjointInterpolationClosedBalls (p h : ℝ → ℝ)
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
              Set.univ.PairwiseDisjoint (fun k : ℕ ↦ Metric.closedBall (orbit.endpoint k)
                (orbit.interpolationRadius Clim Glim k)) := by
  let curve :=
    DFP.TwoLeg.SlowCurve.ofAsymptotics p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, hDisjoint⟩ :=
    DFP.TwoLeg.SlowCurve.pairwiseDisjointInterpolationClosedBalls curve
  have hDisjoint' := hDisjoint
  simp only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] at hDisjoint'
  exact ⟨εbar, hεbar, hDisjoint'⟩

/-- Lemma 5.1 (Isolation radii and pairwise-disjoint interpolation balls) (3):
uniformly over sufficiently small initial scales, every closed interpolation ball is
disjoint from the limiting circle. -/
theorem slowCurveInterpolationClosedBallDisjointLimitCircle (p h : ℝ → ℝ)
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
              ∀ k : ℕ, Disjoint
                (Metric.closedBall (orbit.endpoint k)
                  (orbit.interpolationRadius Clim Glim k))
                (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
  let curve :=
    DFP.TwoLeg.SlowCurve.ofAsymptotics p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, hDisjoint⟩ :=
    DFP.TwoLeg.SlowCurve.interpolationClosedBallDisjointLimitCircle curve
  have hDisjoint' := hDisjoint
  simp only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] at hDisjoint'
  exact ⟨εbar, hεbar, hDisjoint'⟩
