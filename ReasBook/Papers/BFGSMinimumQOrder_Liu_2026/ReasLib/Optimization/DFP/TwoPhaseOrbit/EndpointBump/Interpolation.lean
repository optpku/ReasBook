module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump
public import ReasLib.Analysis.Calculus.ContDiff.AffineCutoffBump.DisjointInterpolation

public section

noncomputable section

namespace DFP.TwoPhaseOrbit

/-- The disjoint endpoint-bump correction vanishes at every endpoint when the interpolation
radii are positive and the interpolation balls are pairwise disjoint. -/
theorem bumpCorrection_endpoint (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ n : ℕ, 0 < orbit.interpolationRadius C G n)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)))
    (k : ℕ) :
    orbit.bumpCorrection C G (orbit.endpoint k) = 0 := by
  rw [bumpCorrection_eq_finsum_scaledLinearBump]
  exact
    (AffineBump.finsum_scaledLinearBump_apply_center
      EuclideanPlane.smoothCutoff EuclideanPlane.tsupport_smoothCutoff_subset
      orbit.endpoint (orbit.interpolationRadius C G)
      (orbit.endpointCorrection C) h_radius h_disjoint k)

/-- The endpoint-bump correction has the prescribed endpoint correction as its Fréchet gradient. -/
theorem bumpCorrection_hasGradientAt_endpoint (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ n : ℕ, 0 < orbit.interpolationRadius C G n)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)))
    (k : ℕ) :
    HasGradientAt (orbit.bumpCorrection C G) (orbit.endpointCorrection C k)
      (orbit.endpoint k) := by
  have hzeroMem :
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ Metric.closedBall 0 (1 / 3 : ℝ) := by
    simp
  have hcutoff0 : EuclideanPlane.smoothCutoff 0 = 1 := by
    exact EuclideanPlane.smoothCutoff_eq_one 0 hzeroMem
  rw [bumpCorrection_eq_finsum_scaledLinearBump]
  exact
    (AffineBump.hasGradientAt_finsum_scaledLinearBump_center
      EuclideanPlane.smoothCutoff EuclideanPlane.contDiff_smoothCutoff hcutoff0
      EuclideanPlane.tsupport_smoothCutoff_subset orbit.endpoint
      (orbit.interpolationRadius C G) (orbit.endpointCorrection C)
      h_radius h_disjoint k)

/-- The canonical gradient of the endpoint-bump correction at an endpoint is its prescribed
endpoint correction vector. -/
theorem bumpCorrection_gradient_endpoint (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ n : ℕ, 0 < orbit.interpolationRadius C G n)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n) (orbit.interpolationRadius C G n)))
    (k : ℕ) :
    gradient (orbit.bumpCorrection C G) (orbit.endpoint k) =
      orbit.endpointCorrection C k := by
  exact (bumpCorrection_hasGradientAt_endpoint orbit C G
    h_radius h_disjoint k).gradient

end DFP.TwoPhaseOrbit
