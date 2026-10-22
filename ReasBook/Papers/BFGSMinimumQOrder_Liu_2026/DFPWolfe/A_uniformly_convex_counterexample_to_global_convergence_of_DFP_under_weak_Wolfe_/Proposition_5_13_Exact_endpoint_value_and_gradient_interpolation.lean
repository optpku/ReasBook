/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Proposition_5_13_Exact_endpoint_value_and_gradient_interpolation.lean
-/

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
