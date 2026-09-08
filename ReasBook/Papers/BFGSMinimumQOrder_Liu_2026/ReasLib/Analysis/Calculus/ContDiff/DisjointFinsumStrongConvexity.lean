module

public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumExtension
public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumHessianBound
public import ReasLib.Analysis.Convex.HessianPerturbation

public section

open Filter Set Topology

universe u

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A twice differentiable zero extension of a disjoint shrinking finsum is strongly convex
after adding a quadratic base whenever the supportwise Hessian is bounded by `η < 1`. -/
theorem strongConvexOn_indicator_compl_finsum_add_halfNormSq_of_decay
    (C : E) (Γset : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → ℝ)
    (η : ℝ) (hη : η < 1) (hη_nonneg : 0 ≤ η)
    (hΓ : IsClosed Γset)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γset)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ 2 (ψ k))
    (hbound : ∀ k z, z ∈ tsupport (ψ k) →
      ‖fderiv ℝ (fderiv ℝ (ψ k)) z‖ ≤ η)
    (hvalue : Tendsto (fun z ↦ ‖∑ᶠ k, ψ k z‖ / Metric.infDist z Γset ^ 2)
      (comap (fun z ↦ Metric.infDist z Γset) (𝓝 0) ⊓ principal Γsetᶜ) (𝓝 0))
    (hderiv : Tendsto (fun z ↦ ‖fderiv ℝ (fun w ↦ ∑ᶠ k, ψ k w) z‖ /
        Metric.infDist z Γset)
      (comap (fun z ↦ Metric.infDist z Γset) (𝓝 0) ⊓ principal Γsetᶜ) (𝓝 0))
    (hsecond : Tendsto
      (fun z ↦ ‖fderiv ℝ (fderiv ℝ (fun w ↦ ∑ᶠ k, ψ k w)) z‖)
      (comap (fun z ↦ Metric.infDist z Γset) (𝓝 0) ⊓ principal Γsetᶜ) (𝓝 0)) :
    StrongConvexOn Set.univ (1 - η)
      (fun y ↦ (1 / 2 : ℝ) * ‖y - C‖ ^ 2 +
        Γsetᶜ.indicator (fun w ↦ ∑ᶠ k, ψ k w) y) := by
  have hΨ : ContDiff ℝ 2
      (Γsetᶜ.indicator (fun w ↦ ∑ᶠ k, ψ k w)) :=
    contDiff_two_indicator_compl_finsum_of_decay Γset x ρ ψ hΓ hcluster hρ hρ0
      hballs hsupport hsmooth hvalue hderiv hsecond
  apply HessianPerturbation.strongConvexOn_halfNormSq_add_of_secondFDeriv_norm_le
    C (Γsetᶜ.indicator (fun w ↦ ∑ᶠ k, ψ k w)) η hΨ hη
  intro y
  exact norm_secondFDeriv_indicator_compl_finsum_le_of_tsupport_bound
    Γset x ρ ψ η hη_nonneg hΓ hcluster hρ hρ0 hballs hsupport hsmooth hbound
      hvalue hderiv y
