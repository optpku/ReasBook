module

public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumBounds
public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumHessianBound

public section

open Filter Topology

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A nonnegative weight bounded by `W` turns a supportwise estimate
`‖iteratedFDeriv ℝ j (ψ k) z‖ ≤ C * w k` into the uniform `C * W` bound
needed by the disjoint-finsum derivative theorem. -/
theorem norm_iteratedFDeriv_finsum_le_of_weighted_tsupport_bound
    (m j : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F)
    (w : ℕ → ℝ) (C W : ℝ) (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hΓ : IsClosed Γ)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k))
    (hweight : ∀ k, 0 ≤ w k ∧ w k ≤ W)
    (hbound : ∀ k z, z ∈ tsupport (ψ k) →
      ‖iteratedFDeriv ℝ j (ψ k) z‖ ≤ C * w k)
    {z : E} (hz : z ∈ Γᶜ) (hj : j ≤ m) :
    ‖iteratedFDeriv ℝ j (fun y ↦ ∑ᶠ k, ψ k y) z‖ ≤ C * W := by
  have huniform : ∀ k z, z ∈ tsupport (ψ k) →
      ‖iteratedFDeriv ℝ j (ψ k) z‖ ≤ C * W := by
    intro k z hzk
    exact (hbound k z hzk).trans
      (mul_le_mul_of_nonneg_left (hweight k).2 hC)
  exact norm_iteratedFDeriv_finsum_le_of_tsupport_bound m j Γ x ρ ψ (C * W)
    (mul_nonneg hC hW) hΓ hcluster hρ hρ0 hballs hsupport hsmooth huniform hz hj

/-- A weighted supportwise second-derivative estimate gives the uniform Hessian bound
for the zero extension of a disjoint finsum, provided the value and first-derivative
decay hypotheses needed at the cluster set are available. -/
theorem norm_secondFDeriv_indicator_compl_finsum_le_of_weighted_tsupport_bound
    (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → ℝ)
    (w : ℕ → ℝ) (C W : ℝ) (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hΓ : IsClosed Γ)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ 2 (ψ k))
    (hweight : ∀ k, 0 ≤ w k ∧ w k ≤ W)
    (hbound : ∀ k z, z ∈ tsupport (ψ k) →
      ‖fderiv ℝ (fderiv ℝ (ψ k)) z‖ ≤ C * w k)
    (hvalue : Tendsto (fun z ↦ ‖∑ᶠ k, ψ k z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0))
    (hderiv : Tendsto (fun z ↦ ‖fderiv ℝ (fun y ↦ ∑ᶠ k, ψ k y) z‖ /
        Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0))
    (z : E) :
    ‖fderiv ℝ (fderiv ℝ (Γᶜ.indicator fun y ↦ ∑ᶠ k, ψ k y)) z‖ ≤ C * W := by
  have huniform : ∀ k y, y ∈ tsupport (ψ k) →
      ‖fderiv ℝ (fderiv ℝ (ψ k)) y‖ ≤ C * W := by
    intro k y hy
    exact (hbound k y hy).trans
      (mul_le_mul_of_nonneg_left (hweight k).2 hC)
  exact norm_secondFDeriv_indicator_compl_finsum_le_of_tsupport_bound Γ x ρ ψ
    (C * W) (mul_nonneg hC hW) hΓ hcluster hρ hρ0 hballs hsupport hsmooth huniform
    hvalue hderiv z
