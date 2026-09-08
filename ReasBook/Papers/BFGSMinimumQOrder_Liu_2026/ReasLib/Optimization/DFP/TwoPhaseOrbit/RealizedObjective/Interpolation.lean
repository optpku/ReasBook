module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.RealizedObjective
public import ReasLib.Optimization.DFP.Iteration
import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump.Interpolation
import ReasLib.Analysis.Convex.HessianPerturbation.Interpolation
import Mathlib.Tactic.Abel

public section

noncomputable section

namespace DFP.TwoPhaseOrbit

/-- The realized objective has the translated quadratic gradient plus the prescribed
endpoint correction at every interpolation endpoint. -/
theorem realizedObjective_hasGradientAt_endpoint (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ n : ℕ, 0 < orbit.interpolationRadius C G n)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)))
    (k : ℕ) :
    HasGradientAt (orbit.realizedObjective C G)
      (orbit.endpoint k - C + orbit.endpointCorrection C k) (orbit.endpoint k) := by
  have hobjective : orbit.realizedObjective C G =
      fun z ↦ (1 / 2 : ℝ) * ‖z - C‖ ^ 2 + orbit.bumpCorrection C G z := by
    funext z
    exact realizedObjective_apply orbit C G z
  rw [hobjective]
  exact HessianPerturbation.hasGradientAt_halfNormSq_sub_add C
    (bumpCorrection_hasGradientAt_endpoint orbit C G h_radius h_disjoint k)

/-- The realized objective agrees with its translated quadratic part at every
interpolation endpoint. -/
theorem realizedObjective_endpoint (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ n : ℕ, 0 < orbit.interpolationRadius C G n)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)))
    (k : ℕ) :
    orbit.realizedObjective C G (orbit.endpoint k) =
      (1 / 2 : ℝ) * ‖orbit.endpoint k - C‖ ^ 2 := by
  rw [realizedObjective_apply]
  exact HessianPerturbation.halfNormSq_sub_add_apply_of_eq_zero C
    (bumpCorrection_endpoint orbit C G h_radius h_disjoint k)

/-- At every interpolation endpoint, the gradient of the realized objective is the
translated quadratic gradient plus the endpoint correction. -/
theorem realizedObjective_gradient_formula_endpoint (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ n : ℕ, 0 < orbit.interpolationRadius C G n)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)))
    (k : ℕ) :
    gradient (orbit.realizedObjective C G) (orbit.endpoint k) =
      orbit.endpoint k - C + orbit.endpointCorrection C k := by
  exact (realizedObjective_hasGradientAt_endpoint orbit C G
    h_radius h_disjoint k).gradient

/-- At every interpolation endpoint, the realized objective has the prescribed
abstract endpoint gradient. -/
theorem realizedObjective_gradient_endpoint (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ n : ℕ, 0 < orbit.interpolationRadius C G n)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)))
    (k : ℕ) :
    gradient (orbit.realizedObjective C G) (orbit.endpoint k) =
      orbit.endpointGradient k := by
  rw [realizedObjective_gradient_formula_endpoint orbit C G
    h_radius h_disjoint k, endpointCorrection_def]
  abel

/-- The successive realized gradients along the endpoints have the same changes as
the prescribed abstract endpoint gradients. -/
theorem realizedObjective_gradientChanges (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ n : ℕ, 0 < orbit.interpolationRadius C G n)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)))
    (k : ℕ) :
    DFP.gradientChanges (DFP.gradients (orbit.realizedObjective C G) orbit.endpoint) k =
      DFP.gradientChanges orbit.endpointGradient k := by
  simp only [DFP.gradientChanges_apply, DFP.gradients_apply]
  rw [realizedObjective_gradient_endpoint orbit C G h_radius h_disjoint (k + 1),
    realizedObjective_gradient_endpoint orbit C G h_radius h_disjoint k]

end DFP.TwoPhaseOrbit
