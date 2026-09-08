module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet
public import Mathlib.Topology.MetricSpace.HausdorffDistance

public section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

/-- A cluster point of a sequence agrees with the sequence limit whenever the latter exists.

This is the basic `EndpointClusterSet/Basic` transport used to identify scalar limits
obtained from radial or angular error estimates. -/
theorem mapClusterPt_eq_of_tendsto
    {X : Type*} [TopologicalSpace X] [T2Space X] [FirstCountableTopology X]
    {u : ℕ → X} {x y : X}
    (hcluster : MapClusterPt x atTop u)
    (hlim : Tendsto u atTop (𝓝 y)) :
    x = y := by
  obtain ⟨ψ, hψ, hψlim⟩ := hcluster.tendsto_subseq
  have hψtop : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hlim' : Tendsto (u ∘ ψ) atTop (𝓝 y) := hlim.comp hψtop
  exact tendsto_nhds_unique hψlim hlim'

/-- A closed nonempty target contains every cluster point whose sequence distance to that
target tends to zero.

This is the metric `EndpointClusterSet/Basic` adapter for converting a radial remainder
estimate into a genuine cluster-set inclusion. -/
theorem mapClusterPt_mem_of_tendsto_infDist
    {X : Type*} [PseudoMetricSpace X]
    {s : Set X} (hs : IsClosed s) (hsne : s.Nonempty)
    {u : ℕ → X} {x : X}
    (hcluster : MapClusterPt x atTop u)
    (hdist : Tendsto (fun n ↦ Metric.infDist (u n) s) atTop (𝓝 0)) :
    x ∈ s := by
  have hscalar :
      MapClusterPt (Metric.infDist x s) atTop
        (fun n ↦ Metric.infDist (u n) s) := by
    simpa only [Function.comp_def] using
      hcluster.continuousAt_comp (Metric.continuous_infDist_pt s).continuousAt
  have hzero : Metric.infDist x s = 0 :=
    mapClusterPt_eq_of_tendsto hscalar hdist
  exact hs.mem_iff_infDist_zero hsne |>.mpr hzero

/-- Every cluster point of an endpoint sequence belongs to a positive-scale limiting circle
when the endpoint distance to that circle tends to zero.

This is the one-sided `EndpointClusterSet/Basic` bridge; equality with the whole circle still
requires a separate angular recurrence or density hypothesis. -/
theorem mapClusterSet_subset_limitCircle_of_tendsto_infDist
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (hG : 0 < G)
    {u : ℕ → EuclideanSpace ℝ (Fin 2)}
    (hdist : ∀ x, MapClusterPt x atTop u →
      Tendsto (fun n ↦ Metric.infDist (u n) (limitCircle C G)) atTop (𝓝 0)) :
    {x : EuclideanSpace ℝ (Fin 2) | MapClusterPt x atTop u} ⊆ limitCircle C G := by
  intro x hx
  exact mapClusterPt_mem_of_tendsto_infDist
    (isClosed_limitCircle C G hG)
    (limitCircle_nonempty C G hG)
    hx (hdist x hx)

end DFP.TwoPhaseOrbit
