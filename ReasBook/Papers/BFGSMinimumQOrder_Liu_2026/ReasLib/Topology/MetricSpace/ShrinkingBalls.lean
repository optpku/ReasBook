module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Sequences

public section

open Filter Topology

universe u

namespace Metric

/-- Shrinking closed balls are locally finite at every point outside the set containing all
`atTop` cluster points of their centers. -/
theorem locallyFinite_closedBall_outside {X : Type u} [MetricSpace X] (Γ : Set X)
    (x : ℕ → X) (ρ : ℕ → ℝ) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ) :
    ∀ z ∈ Γᶜ, ∃ s ∈ 𝓝 z,
      {k | (closedBall (x k) (ρ k) ∩ s).Nonempty}.Finite := by
  classical
  intro z hz
  -- Route correction: exclude `z` itself as a cluster point, without requiring closedness of `Γ`.
  have hzcluster : ¬ MapClusterPt z atTop x := by
    intro hzcluster
    exact hz (hcluster z hzcluster)
  -- A metric-basis neighborhood is therefore eventually avoided by the centers.
  rw [Metric.nhds_basis_ball.mapClusterPt_iff_frequently] at hzcluster
  push Not at hzcluster
  obtain ⟨r, hr, hravoid⟩ := hzcluster
  have hcenters : ∀ᶠ k in atTop, x k ∉ ball z r :=
    hravoid
  -- The radii are eventually smaller than half of the exclusion radius.
  have hradii : ∀ᶠ k in atTop, ρ k < r / 2 :=
    hρ0.eventually_lt_const (half_pos hr)
  -- Combining the estimates makes every sufficiently late closed ball
  -- miss a fixed neighborhood.
  have hlate : ∀ᶠ k in atTop,
      ¬ (closedBall (x k) (ρ k) ∩ ball z (r / 2)).Nonempty := by
    filter_upwards [hcenters, hradii] with k hkcenter hkradius
    have hcenterDist : r ≤ dist (x k) z := by
      simpa only [Metric.mem_ball, not_lt] using hkcenter
    have hseparated : ρ k + r / 2 ≤ dist (x k) z := by
      linarith
    intro hinter
    rcases hinter with ⟨w, hwclosed, hwball⟩
    exact Set.disjoint_left.mp (closedBall_disjoint_ball hseparated) hwclosed hwball
  refine ⟨ball z (r / 2), ball_mem_nhds z (half_pos hr), ?_⟩
  -- Eventual emptiness at `atTop` says precisely that the exceptional indices are finite.
  rw [← Nat.cofinite_eq_atTop] at hlate
  simpa only [not_not] using Filter.eventually_cofinite.mp hlate

end Metric
