/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_5_3a_Pointwise_summability_and_unique_active_bump.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump

public section

noncomputable section

open Set

namespace DFP.TwoPhaseOrbit

/- Lemma 5.3a (Pointwise summability and unique active bump)
The endpoint-bump family is pointwise summable, with at most one active bump
and a tsum equal to the corresponding correction. -/
#check (DFP.TwoPhaseOrbit.endpointBump_activeIndices_subsingleton :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    (∀ k : ℕ, 0 < orbit.interpolationRadius C G k) →
    Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k)) →
    ∀ z : EuclideanSpace ℝ (Fin 2),
      (Function.support (fun k : ℕ ↦ orbit.endpointBump C G k z)).Subsingleton)

#check (DFP.TwoPhaseOrbit.endpointBump_summable :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    (∀ k : ℕ, 0 < orbit.interpolationRadius C G k) →
    Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k)) →
    ∀ z : EuclideanSpace ℝ (Fin 2),
      Summable (fun k : ℕ ↦ orbit.endpointBump C G k z))

#check (DFP.TwoPhaseOrbit.endpointBump_tsum_eq_of_ne_zero :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    (∀ k : ℕ, 0 < orbit.interpolationRadius C G k) →
    Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k)) →
    ∀ (z : EuclideanSpace ℝ (Fin 2)) (k : ℕ),
      orbit.endpointBump C G k z ≠ 0 →
        (∑' n : ℕ, orbit.endpointBump C G n z) = orbit.endpointBump C G k z)

#check (DFP.TwoPhaseOrbit.bumpCorrection_eq_tsum :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    (∀ k : ℕ, 0 < orbit.interpolationRadius C G k) →
    Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k)) →
    ∀ z : EuclideanSpace ℝ (Fin 2),
      orbit.bumpCorrection C G z = ∑' k : ℕ, orbit.endpointBump C G k z)

/-- Lemma 5.3a (Pointwise summability and unique active bump) (4): when every
endpoint bump vanishes at `z`, their pointwise tsum is zero. -/
theorem endpointBump_tsum_eq_zero (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (_h_radius : ∀ k : ℕ, 0 < orbit.interpolationRadius C G k)
    (_h_disjoint : Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k)))
    (z : EuclideanSpace ℝ (Fin 2))
    (h_zero : ∀ k : ℕ, orbit.endpointBump C G k z = 0) :
    (∑' k : ℕ, orbit.endpointBump C G k z) = 0 := by
  exact DisjointFinsum.tsum_eq_zero_of_forall_eq_zero
    (fun k : ℕ ↦ orbit.endpointBump C G k z) h_zero

end DFP.TwoPhaseOrbit
