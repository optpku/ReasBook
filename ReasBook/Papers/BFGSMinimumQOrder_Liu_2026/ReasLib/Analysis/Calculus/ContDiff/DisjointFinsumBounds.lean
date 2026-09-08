module

public import ReasLib.Analysis.Calculus.ShrinkingSupportFinsum

public section

open Filter Topology

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A uniform bound for one iterated derivative on each summand's topological support
gives the same bound for the pointwise finsum away from the cluster set. -/
theorem norm_iteratedFDeriv_finsum_le_of_tsupport_bound
    (m j : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F)
    (C : ℝ) (hC : 0 ≤ C) (hΓ : IsClosed Γ)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ) (hρ : ∀ k, 0 ≤ ρ k)
    (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k))
    (hbound : ∀ k z, z ∈ tsupport (ψ k) → ‖iteratedFDeriv ℝ j (ψ k) z‖ ≤ C)
    {z : E} (hz : z ∈ Γᶜ) (hj : j ≤ m) :
    ‖iteratedFDeriv ℝ j (fun w ↦ ∑ᶠ n, ψ n w) z‖ ≤ C := by
  by_cases hactive : ∃ k, z ∈ tsupport (ψ k)
  · obtain ⟨k, hzk⟩ := hactive
    rw [iteratedFDeriv_finsum_eq_of_mem_tsupport Γ x ρ ψ hcluster hρ0 hballs hsupport hz
      (k := k) (j := j) hzk]
    exact hbound k z hzk
  · rw [iteratedFDeriv_finsum_eq_zero Γ x ρ ψ hcluster hρ0 hsupport hz
      (j := j) (not_exists.mp hactive), norm_zero]
    exact hC
