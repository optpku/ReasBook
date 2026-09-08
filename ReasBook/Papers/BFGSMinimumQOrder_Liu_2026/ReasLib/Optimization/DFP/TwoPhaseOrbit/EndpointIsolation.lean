module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet
public import ReasLib.Topology.MetricSpace.Isolation

public section

noncomputable section

namespace DFP.TwoPhaseOrbit

/-- The distance from endpoint `k` to the limiting circle and all other endpoints. -/
def isolationDistance (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ) : ℝ :=
  Metric.isolationDistance (orbit.closedSetCandidate C G) (orbit.endpoint k)

/-- The endpoint isolation distance is the infimum distance to the punctured endpoint set. -/
theorem isolationDistance_def (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ) :
    orbit.isolationDistance C G k = Metric.infDist (orbit.endpoint k)
      (orbit.closedSetCandidate C G \ {orbit.endpoint k}) := by
  rw [isolationDistance]
  exact Metric.isolationDistance_eq _ _

/-- Endpoint isolation distance is nonnegative. -/
theorem isolationDistance_nonneg (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ) :
    0 ≤ orbit.isolationDistance C G k := by
  exact Metric.isolationDistance_nonneg
    (orbit.closedSetCandidate C G) (orbit.endpoint k)

/-- The interpolation radius at an endpoint is one quarter of its isolation distance. -/
def interpolationRadius (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ) : ℝ :=
  Metric.isolationRadius (orbit.closedSetCandidate C G) (orbit.endpoint k)

/-- The endpoint interpolation radius is the generic metric isolation radius in
the endpoint closed-set candidate. -/
@[simp]
theorem interpolationRadius_eq_isolationRadius (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ) :
    orbit.interpolationRadius C G k =
      Metric.isolationRadius (orbit.closedSetCandidate C G) (orbit.endpoint k) := by
  rfl

/-- The interpolation radius is one quarter of the infimum distance to the punctured
endpoint set. -/
theorem interpolationRadius_def (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ) :
    orbit.interpolationRadius C G k = Metric.infDist (orbit.endpoint k)
      (orbit.closedSetCandidate C G \ {orbit.endpoint k}) / 4 := by
  rw [interpolationRadius_eq_isolationRadius]
  exact Metric.isolationRadius_eq _ _

/-- The interpolation radius is one quarter of the endpoint isolation
distance. -/
theorem interpolationRadius_eq_isolationDistance_div (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ) :
    orbit.interpolationRadius C G k = orbit.isolationDistance C G k / 4 := by
  rw [interpolationRadius_eq_isolationRadius, Metric.isolationRadius_eq,
    isolationDistance_def]

/-- Endpoint interpolation radii are nonnegative. -/
theorem interpolationRadius_nonneg (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ) :
    0 ≤ orbit.interpolationRadius C G k := by
  exact Metric.isolationRadius_nonneg
    (orbit.closedSetCandidate C G) (orbit.endpoint k)

/-- A positive endpoint isolation distance strictly exceeds its interpolation
radius. -/
theorem interpolationRadius_lt_isolationDistance (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ)
    (hpos : 0 < orbit.isolationDistance C G k) :
    orbit.interpolationRadius C G k < orbit.isolationDistance C G k := by
  exact Metric.isolationRadius_lt_isolationDistance
    (orbit.closedSetCandidate C G) (orbit.endpoint k) hpos

/-- Injectivity of the endpoint sequence makes its closed interpolation balls
pairwise disjoint. -/
theorem pairwiseDisjoint_interpolationClosedBall (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (hinj : Function.Injective orbit.endpoint) :
    Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k)) := by
  have hendpointMem (k : ℕ) :
      orbit.endpoint k ∈ orbit.closedSetCandidate C G :=
    mem_closedSetCandidate.mpr (Or.inr ⟨k, rfl⟩)
  simpa only [interpolationRadius_eq_isolationRadius] using
    (Metric.pairwiseDisjoint_isolationClosedBall
      (orbit.closedSetCandidate C G) orbit.endpoint hendpointMem hinj)

/-- A positive endpoint isolation distance makes its interpolation ball
disjoint from the limiting circle, provided the endpoint is not on that
circle. -/
theorem interpolationClosedBall_disjoint_limitCircle (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ)
    (hpos : 0 < orbit.isolationDistance C G k)
    (hnot : orbit.endpoint k ∉ limitCircle C G) :
    Disjoint
      (Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k))
      (limitCircle C G) := by
  have hcircleSubset : limitCircle C G ⊆
      orbit.closedSetCandidate C G \ {orbit.endpoint k} := by
    intro y hy
    refine ⟨mem_closedSetCandidate.mpr (Or.inl hy), ?_⟩
    have hyne : y ≠ orbit.endpoint k := by
      intro hyEq
      apply hnot
      simpa only [hyEq] using hy
    simpa only [Set.mem_singleton_iff] using hyne
  have hradius : Metric.isolationRadius (orbit.closedSetCandidate C G)
      (orbit.endpoint k) < Metric.infDist (orbit.endpoint k)
        (orbit.closedSetCandidate C G \ {orbit.endpoint k}) := by
    have hlt := Metric.isolationRadius_lt_isolationDistance
      (orbit.closedSetCandidate C G) (orbit.endpoint k) hpos
    simpa only [Metric.isolationDistance_eq] using hlt
  have hpunctured : Disjoint
      (Metric.closedBall (orbit.endpoint k)
        (Metric.isolationRadius (orbit.closedSetCandidate C G) (orbit.endpoint k)))
      (orbit.closedSetCandidate C G \ {orbit.endpoint k}) :=
    Metric.disjoint_closedBall_of_lt_infDist hradius
  simpa only [interpolationRadius_eq_isolationRadius] using
    (Disjoint.mono_right hcircleSubset hpunctured)

end DFP.TwoPhaseOrbit
