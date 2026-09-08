module

public import ReasLib.Analysis.Calculus.ContDiff.AffineCutoffBump
public import ReasLib.Analysis.Calculus.EuclideanPlaneSmoothCutoff
public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumSummable
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointCorrection
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointIsolation

public section

open scoped ContDiff

noncomputable section

namespace DFP.TwoPhaseOrbit

/-- The cutoff bump centered at endpoint `k`, scaled by its interpolation radius and
weighted by its endpoint correction vector. -/
def endpointBump (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  AffineBump.scaledLinearBump EuclideanPlane.smoothCutoff (orbit.endpoint k)
    (orbit.interpolationRadius C G k) (orbit.endpointCorrection C k)

/-- The endpoint bump is the generic scaled linear bump specialized to the endpoint data. -/
theorem endpointBump_eq_scaledLinearBump (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ) :
    orbit.endpointBump C G k =
      AffineBump.scaledLinearBump EuclideanPlane.smoothCutoff (orbit.endpoint k)
        (orbit.interpolationRadius C G k) (orbit.endpointCorrection C k) := by
  rfl

/-- Every endpoint bump is infinitely continuously differentiable, independently
of the endpoint data and interpolation radius. -/
theorem contDiff_endpointBump (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ) :
    ContDiff ℝ ∞ (orbit.endpointBump C G k) := by
  rw [endpointBump_eq_scaledLinearBump]
  exact AffineBump.contDiff_scaledLinearBump EuclideanPlane.smoothCutoff
    EuclideanPlane.contDiff_smoothCutoff (orbit.endpoint k)
      (orbit.interpolationRadius C G k) (orbit.endpointCorrection C k)

/-- Evaluation of the cutoff bump attached to an endpoint. -/
theorem endpointBump_apply (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ) (z : EuclideanSpace ℝ (Fin 2)) :
    orbit.endpointBump C G k z =
      EuclideanPlane.smoothCutoff
          ((orbit.interpolationRadius C G k)⁻¹ • (z - orbit.endpoint k)) *
        inner ℝ (orbit.endpointCorrection C k) (z - orbit.endpoint k) := by
  rw [endpointBump_eq_scaledLinearBump, AffineBump.scaledLinearBump_apply]

/-- The pointwise infinite sum of all endpoint cutoff bumps. -/
def bumpCorrection (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun z ↦ ∑ᶠ k, orbit.endpointBump C G k z

/-- Evaluation of the global bump correction as a pointwise finsum. -/
theorem bumpCorrection_apply (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    orbit.bumpCorrection C G z = ∑ᶠ k, orbit.endpointBump C G k z := by
  rfl

/-- The global bump correction is the pointwise finsum of the corresponding
generic scaled linear bumps. -/
theorem bumpCorrection_eq_finsum_scaledLinearBump (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) :
    orbit.bumpCorrection C G = fun z ↦ ∑ᶠ k,
      AffineBump.scaledLinearBump EuclideanPlane.smoothCutoff (orbit.endpoint k)
        (orbit.interpolationRadius C G k) (orbit.endpointCorrection C k) z := by
  funext z
  rw [bumpCorrection_apply]
  apply congrArg (fun f : ℕ → ℝ ↦ ∑ᶠ k, f k)
  funext k
  exact congrFun (endpointBump_eq_scaledLinearBump orbit C G k) z

/-- The topological support of an endpoint bump lies in its interpolation closed ball. -/
theorem endpointBump_tsupport_subset_interpolationClosedBall
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ k : ℕ, 0 < orbit.interpolationRadius C G k) (k : ℕ) :
    tsupport (orbit.endpointBump C G k) ⊆
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k) := by
  rw [DFP.TwoPhaseOrbit.endpointBump_eq_scaledLinearBump]
  exact AffineBump.tsupport_scaledLinearBump_subset_closedBall
    EuclideanPlane.smoothCutoff EuclideanPlane.tsupport_smoothCutoff_subset
      (orbit.endpoint k) (orbit.interpolationRadius C G k)
      (orbit.endpointCorrection C k) (h_radius k)

/-- Pairwise-disjoint interpolation balls give pairwise-disjoint endpoint-bump supports. -/
theorem endpointBump_pairwiseDisjoint_tsupport
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ k : ℕ, 0 < orbit.interpolationRadius C G k)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k))) :
    Set.univ.PairwiseDisjoint (fun k : ℕ ↦ tsupport (orbit.endpointBump C G k)) :=
  h_disjoint.mono (endpointBump_tsupport_subset_interpolationClosedBall orbit C G h_radius)

/-- At each point, at most one endpoint bump has a nonzero value. -/
theorem endpointBump_activeIndices_subsingleton (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ k : ℕ, 0 < orbit.interpolationRadius C G k)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k)))
    (z : EuclideanSpace ℝ (Fin 2)) :
    (Function.support (fun k : ℕ ↦ orbit.endpointBump C G k z)).Subsingleton := by
  exact DisjointFinsum.support_apply_subsingleton_of_pairwiseDisjoint_tsupport
    (fun k : ℕ ↦ orbit.endpointBump C G k)
    (endpointBump_pairwiseDisjoint_tsupport orbit C G h_radius h_disjoint) z

/-- At each point, the endpoint-bump family is summable. -/
theorem endpointBump_summable (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ k : ℕ, 0 < orbit.interpolationRadius C G k)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k)))
    (z : EuclideanSpace ℝ (Fin 2)) :
    Summable (fun k : ℕ ↦ orbit.endpointBump C G k z) := by
  exact DisjointFinsum.summable_apply_of_pairwiseDisjoint_tsupport
    (fun k : ℕ ↦ orbit.endpointBump C G k)
    (endpointBump_pairwiseDisjoint_tsupport orbit C G h_radius h_disjoint) z

/-- If endpoint bump `k` is nonzero at a point, the pointwise tsum is that bump. -/
theorem endpointBump_tsum_eq_of_ne_zero (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ k : ℕ, 0 < orbit.interpolationRadius C G k)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k)))
    (z : EuclideanSpace ℝ (Fin 2)) (k : ℕ)
    (h_active : orbit.endpointBump C G k z ≠ 0) :
    (∑' n : ℕ, orbit.endpointBump C G n z) = orbit.endpointBump C G k z := by
  exact DisjointFinsum.tsum_eq_single_of_support_subsingleton
    (fun n : ℕ ↦ orbit.endpointBump C G n z) k h_active
    (endpointBump_activeIndices_subsingleton orbit C G h_radius h_disjoint z)

/-- The finsum-defined endpoint correction equals the pointwise endpoint-bump tsum. -/
theorem bumpCorrection_eq_tsum (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ k : ℕ, 0 < orbit.interpolationRadius C G k)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k)))
    (z : EuclideanSpace ℝ (Fin 2)) :
    orbit.bumpCorrection C G z = ∑' k : ℕ, orbit.endpointBump C G k z := by
  rw [DFP.TwoPhaseOrbit.bumpCorrection_apply]
  exact (tsum_eq_finsum
    (endpointBump_activeIndices_subsingleton orbit C G h_radius h_disjoint z).finite).symm

end DFP.TwoPhaseOrbit
