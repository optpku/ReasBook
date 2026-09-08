module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit
public import ReasLib.Topology.MetricSpace.Sphere
public import ReasLib.Topology.Sequences
public import Mathlib.Analysis.Normed.Module.FiniteDimension

public section

noncomputable section

open Filter

namespace DFP.TwoPhaseOrbit

/-- The flattened sequence of boundary and middle endpoints of a two-phase orbit. -/
def endpoint (orbit : DFP.TwoPhaseOrbit) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  let s := orbit.state (k / 2)
  if k % 2 = 0 then s.point else s.middlePoint

/-- The even flattened endpoint is the corresponding cycle-boundary point. -/
theorem endpoint_even (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpoint (2 * j) = (orbit.state j).point := by
  rw [endpoint.eq_1]
  simp

/-- The odd flattened endpoint is the corresponding middle point. -/
theorem endpoint_odd (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpoint (2 * j + 1) = (orbit.state j).middlePoint := by
  rw [endpoint.eq_1]
  have hdiv : (2 * j + 1) / 2 = j := by omega
  rw [hdiv]
  simp

/-- The affine image of the planar unit sphere with center `C` and scale `G`. -/
def limitCircle (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  (fun v ↦ C + G • v) '' Metric.sphere 0 1

/-- Membership in the limiting circle in its affine unit-vector form. -/
theorem mem_limitCircle {C x : EuclideanSpace ℝ (Fin 2)} {G : ℝ} :
    x ∈ limitCircle C G ↔ ∃ v, ‖v‖ = 1 ∧ C + G • v = x := by
  rw [limitCircle.eq_1]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, by simpa [Metric.mem_sphere] using hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, by simpa [Metric.mem_sphere] using hv, rfl⟩

/-- A limiting circle with positive scale is the corresponding metric sphere. -/
theorem limitCircle_eq_sphere (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (hG : 0 < G) :
    limitCircle C G = Metric.sphere C G := by
  rw [limitCircle.eq_1]
  exact Metric.affinity_unitSphere C G hG

/-- A positive-scale limiting circle is nonempty. -/
theorem limitCircle_nonempty (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (hG : 0 < G) :
    (limitCircle C G).Nonempty := by
  rw [limitCircle_eq_sphere C G hG]
  exact NormedSpace.sphere_nonempty.mpr hG.le

/-- A positive-scale limiting circle is compact. -/
theorem isCompact_limitCircle (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (hG : 0 < G) :
    IsCompact (limitCircle C G) := by
  rw [limitCircle_eq_sphere C G hG]
  exact isCompact_sphere C G

/-- A limiting circle with positive scale is closed. -/
theorem isClosed_limitCircle (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (hG : 0 < G) :
    IsClosed (limitCircle C G) := by
  rw [limitCircle_eq_sphere C G hG]
  exact Metric.isClosed_sphere

/-- The limiting circle together with every endpoint of a two-phase orbit. -/
def closedSetCandidate (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2))
    (G : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  limitCircle C G ∪ Set.range orbit.endpoint

/-- The endpoint closed-set candidate is the union of its limiting circle and
the range of the flattened endpoint sequence. -/
theorem closedSetCandidate_eq (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) :
    orbit.closedSetCandidate C G = limitCircle C G ∪ Set.range orbit.endpoint := by
  rfl

/-- Membership in the endpoint closed-set candidate. -/
theorem mem_closedSetCandidate {orbit : DFP.TwoPhaseOrbit}
    {C x : EuclideanSpace ℝ (Fin 2)} {G : ℝ} :
    x ∈ orbit.closedSetCandidate C G ↔
      x ∈ limitCircle C G ∨ ∃ k : ℕ, orbit.endpoint k = x := by
  rw [closedSetCandidate_eq]
  rfl

/-- The endpoint candidate is closed when all endpoint cluster points lie on its
limiting circle. -/
theorem isClosed_closedSetCandidate (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (hG : 0 < G)
    (hcluster : ∀ x, MapClusterPt x atTop orbit.endpoint → x ∈ limitCircle C G) :
    IsClosed (orbit.closedSetCandidate C G) := by
  rw [closedSetCandidate_eq]
  exact (isClosed_limitCircle C G hG).union_range_of_mapClusterPt orbit.endpoint hcluster

end DFP.TwoPhaseOrbit
