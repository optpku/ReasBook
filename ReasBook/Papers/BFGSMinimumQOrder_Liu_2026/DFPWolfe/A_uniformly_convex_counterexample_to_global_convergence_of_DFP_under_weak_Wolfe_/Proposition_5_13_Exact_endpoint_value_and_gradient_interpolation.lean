module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.RealizedObjective.Interpolation

public section

#check (DFP.TwoPhaseOrbit.realizedObjective_hasGradientAt_endpoint :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    (∀ n : ℕ, 0 < orbit.interpolationRadius C G n) →
    Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)) →
    ∀ k : ℕ, HasGradientAt (orbit.realizedObjective C G)
      (orbit.endpoint k - C + orbit.endpointCorrection C k) (orbit.endpoint k))

/- Proposition 5.13 (Exact endpoint value and gradient interpolation), eq:endpoint-data:
the realized objective has the translated quadratic value at every endpoint. -/
#check (DFP.TwoPhaseOrbit.realizedObjective_endpoint :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    (∀ n : ℕ, 0 < orbit.interpolationRadius C G n) →
    Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)) →
    ∀ k : ℕ, orbit.realizedObjective C G (orbit.endpoint k) =
      (1 / 2 : ℝ) * ‖orbit.endpoint k - C‖ ^ 2)

#check (DFP.TwoPhaseOrbit.realizedObjective_gradient_formula_endpoint :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    (∀ n : ℕ, 0 < orbit.interpolationRadius C G n) →
    Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)) →
    ∀ k : ℕ, gradient (orbit.realizedObjective C G) (orbit.endpoint k) =
      orbit.endpoint k - C + orbit.endpointCorrection C k)

#check (DFP.TwoPhaseOrbit.realizedObjective_gradient_endpoint :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    (∀ n : ℕ, 0 < orbit.interpolationRadius C G n) →
    Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)) →
    ∀ k : ℕ, gradient (orbit.realizedObjective C G) (orbit.endpoint k) =
      orbit.endpointGradient k)

#check (DFP.TwoPhaseOrbit.realizedObjective_gradientChanges :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    (∀ n : ℕ, 0 < orbit.interpolationRadius C G n) →
    Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)) →
    ∀ k : ℕ,
      DFP.gradientChanges (DFP.gradients (orbit.realizedObjective C G) orbit.endpoint) k =
        DFP.gradientChanges orbit.endpointGradient k)
