module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Wolfe

public section

open Filter
open scoped Asymptotics Topology

/- Uniformly over both phases, the realized objective decrease ratio is at
least `1 / 2`, with positive predicted decrease, on every sufficiently small
slow-curve orbit. -/
#check (DFP.TwoPhaseOrbit.slowCurvePhaseDecreaseRatioLowerBound :
  (p h : ℝ → ℝ) →
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ G : ℝ,
            (∀ n : ℕ, 0 < orbit.interpolationRadius Clim G n) →
              Set.univ.PairwiseDisjoint (fun n : ℕ ↦
                Metric.closedBall (orbit.endpoint n)
                  (orbit.interpolationRadius Clim G n)) →
                ∀ j : ℕ, ∀ i : Fin 2,
                  let k := 2 * j + i.val
                  let s := orbit.endpoint (k + 1) - orbit.endpoint k
                  let q := -inner ℝ (orbit.endpointGradient k) s
                  0 < q ∧
                    (1 / 2 : ℝ) ≤
                      (orbit.realizedObjective Clim G (orbit.endpoint k) -
                        orbit.realizedObjective Clim G (orbit.endpoint (k + 1))) / q)

/- Lemma 6.3 (Armijo inequality with $c_1=1/4$): every sufficiently small slow-curve orbit satisfies Armijo with coefficient `1 / 4`. -/
#check (DFP.TwoPhaseOrbit.slowCurveArmijo :
  (p h : ℝ → ℝ) →
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ G : ℝ,
            (∀ n : ℕ, 0 < orbit.interpolationRadius Clim G n) →
              Set.univ.PairwiseDisjoint (fun n : ℕ ↦
                Metric.closedBall (orbit.endpoint n)
                  (orbit.interpolationRadius Clim G n)) →
                ∀ k : ℕ,
                  let s := orbit.endpoint (k + 1) - orbit.endpoint k
                  orbit.realizedObjective Clim G (orbit.endpoint (k + 1)) ≤
                    orbit.realizedObjective Clim G (orbit.endpoint k) +
                      (1 / 4 : ℝ) *
                        inner ℝ (orbit.endpointGradient k) s)
