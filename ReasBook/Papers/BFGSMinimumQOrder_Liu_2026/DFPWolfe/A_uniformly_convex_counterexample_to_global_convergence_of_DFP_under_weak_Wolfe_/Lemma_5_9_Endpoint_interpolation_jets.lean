module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump.Interpolation

public section

noncomputable section

/- Lemma 5.9 (Endpoint interpolation jets) -/
#check (DFP.TwoPhaseOrbit.bumpCorrection_endpoint :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    (∀ n : ℕ, 0 < orbit.interpolationRadius C G n) →
    Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)) →
    ∀ k : ℕ, orbit.bumpCorrection C G (orbit.endpoint k) = 0)

#check (DFP.TwoPhaseOrbit.bumpCorrection_hasGradientAt_endpoint :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    (∀ n : ℕ, 0 < orbit.interpolationRadius C G n) →
    Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)) →
    ∀ k : ℕ, HasGradientAt (orbit.bumpCorrection C G)
      (orbit.endpointCorrection C k) (orbit.endpoint k))

/- Lemma 5.9 (Endpoint interpolation jets) -/
#check (DFP.TwoPhaseOrbit.bumpCorrection_gradient_endpoint :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    (∀ n : ℕ, 0 < orbit.interpolationRadius C G n) →
    Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)) →
    ∀ k : ℕ, gradient (orbit.bumpCorrection C G) (orbit.endpoint k) =
      orbit.endpointCorrection C k)
