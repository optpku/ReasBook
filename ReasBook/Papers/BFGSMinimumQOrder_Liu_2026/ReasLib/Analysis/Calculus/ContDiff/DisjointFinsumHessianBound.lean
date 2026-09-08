module

public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumBounds
public import ReasLib.Analysis.Calculus.ContDiff.ZeroExtension

public section

open Filter Set Topology

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The norm of the ordinary second Fréchet derivative agrees with the norm of the
order-two iterated Fréchet derivative. -/
theorem norm_secondFDeriv_eq_norm_iteratedFDeriv_two (f : E → F) (z : E) :
    ‖fderiv ℝ (fderiv ℝ f) z‖ = ‖iteratedFDeriv ℝ 2 f z‖ := by
  calc
    ‖fderiv ℝ (fderiv ℝ f) z‖ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ f) z‖ :=
      (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ f)).symm
    _ = ‖iteratedFDeriv ℝ 2 f z‖ :=
      norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (n := 1)

/-- A supportwise Hessian bound for disjoint shrinking summands gives the same global
bound after their pointwise finsum is extended by zero across the closed cluster set. -/
theorem norm_secondFDeriv_indicator_compl_finsum_le_of_tsupport_bound
    (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F)
    (C : ℝ) (hC : 0 ≤ C) (hΓ : IsClosed Γ)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ) (hρ : ∀ k, 0 ≤ ρ k)
    (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ 2 (ψ k))
    (hbound : ∀ k z, z ∈ tsupport (ψ k) →
      ‖fderiv ℝ (fderiv ℝ (ψ k)) z‖ ≤ C)
    (hvalue : Tendsto (fun z ↦ ‖∑ᶠ k, ψ k z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0))
    (hderiv : Tendsto (fun z ↦ ‖fderiv ℝ (fun w ↦ ∑ᶠ k, ψ k w) z‖ /
        Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0))
    (z : E) :
    ‖fderiv ℝ (fderiv ℝ (Γᶜ.indicator fun w ↦ ∑ᶠ k, ψ k w)) z‖ ≤ C := by
  have hsmoothOutside : ContDiffOn ℝ 2 (fun w ↦ ∑ᶠ k, ψ k w) Γᶜ :=
    contDiffOn_finsum_outside 2 Γ x ρ ψ hΓ hcluster hρ0 hsupport hsmooth
  have hboundIterated : ∀ k w, w ∈ tsupport (ψ k) →
      ‖iteratedFDeriv ℝ 2 (ψ k) w‖ ≤ C := by
    intro k w hw
    rw [← norm_secondFDeriv_eq_norm_iteratedFDeriv_two]
    exact hbound k w hw
  rw [IsClosed.fderiv_fderiv_indicator_compl Γ (fun w ↦ ∑ᶠ k, ψ k w) hΓ
    hsmoothOutside hvalue hderiv]
  by_cases hz : z ∈ Γᶜ
  · rw [indicator_of_mem hz, norm_secondFDeriv_eq_norm_iteratedFDeriv_two]
    exact norm_iteratedFDeriv_finsum_le_of_tsupport_bound 2 2 Γ x ρ ψ C hC hΓ
      hcluster hρ hρ0 hballs hsupport hsmooth hboundIterated hz le_rfl
  · rw [indicator_of_notMem hz, norm_zero]
    exact hC
