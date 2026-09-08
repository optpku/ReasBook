module

public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumBounds

public section

open Filter Topology

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- At an active center outside the cluster set, every available iterated derivative of a
pointwise finsum equals the corresponding derivative of the centered summand. -/
theorem iteratedFDeriv_finsum_eq_at_center
    (m : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F)
    (hΓ : IsClosed Γ) (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k)) (k j : ℕ) (hxk : x k ∈ Γᶜ)
    (hcenter : x k ∈ tsupport (ψ k)) (hj : j ≤ m) :
    iteratedFDeriv ℝ j (fun w ↦ ∑ᶠ n, ψ n w) (x k) =
      iteratedFDeriv ℝ j (ψ k) (x k) := by
  exact iteratedFDeriv_finsum_eq_of_mem_tsupport Γ x ρ ψ hcluster hρ0 hballs hsupport hxk
    (k := k) (j := j) hcenter

/-- A uniform bound for the iterated derivatives of centered summands gives the same bound
for the corresponding derivative of the pointwise finsum at every active center. -/
theorem norm_iteratedFDeriv_finsum_at_center_le
    (m j : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F)
    (C : ℝ) (hΓ : IsClosed Γ) (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k)) (hx : ∀ k, x k ∈ Γᶜ)
    (hcenter : ∀ k, x k ∈ tsupport (ψ k))
    (hbound : ∀ k, ‖iteratedFDeriv ℝ j (ψ k) (x k)‖ ≤ C) (hj : j ≤ m) :
    ∀ k, ‖iteratedFDeriv ℝ j (fun w ↦ ∑ᶠ n, ψ n w) (x k)‖ ≤ C := by
  intro k
  rw [iteratedFDeriv_finsum_eq_at_center m Γ x ρ ψ hΓ hcluster hρ hρ0 hballs
    hsupport hsmooth k j (hx k) (hcenter k) hj]
  exact hbound k
