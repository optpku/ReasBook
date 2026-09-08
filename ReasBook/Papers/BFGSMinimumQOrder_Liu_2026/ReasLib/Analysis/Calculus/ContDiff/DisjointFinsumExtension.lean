module

public import ReasLib.Analysis.Calculus.ContDiff.ZeroExtension
public import ReasLib.Analysis.Calculus.ShrinkingSupportFinsum

public section

open Filter Topology

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A pointwise finsum over shrinking pairwise-disjoint supports extends by zero across its
closed cluster set as a globally twice continuously differentiable function, provided its
value and first two derivatives have the required boundary decay. -/
theorem contDiff_two_indicator_compl_finsum_of_decay
    (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F) (hΓ : IsClosed Γ)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ) (hρ : ∀ k, 0 ≤ ρ k)
    (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ 2 (ψ k))
    (hvalue : Tendsto (fun z ↦ ‖∑ᶠ k, ψ k z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0))
    (hderiv : Tendsto (fun z ↦ ‖fderiv ℝ (fun w ↦ ∑ᶠ k, ψ k w) z‖ /
        Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0))
    (hsecond : Tendsto
      (fun z ↦ ‖fderiv ℝ (fderiv ℝ (fun w ↦ ∑ᶠ k, ψ k w)) z‖)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0)) :
    ContDiff ℝ 2 (Γᶜ.indicator fun z ↦ ∑ᶠ k, ψ k z) := by
  have hsmoothOutside : ContDiffOn ℝ 2 (fun z ↦ ∑ᶠ k, ψ k z) Γᶜ :=
    contDiffOn_finsum_outside 2 Γ x ρ ψ hΓ hcluster hρ0 hsupport hsmooth
  exact IsClosed.contDiff_two_indicator_compl Γ (fun z ↦ ∑ᶠ k, ψ k z) hΓ
    hsmoothOutside hvalue hderiv hsecond
