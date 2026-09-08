module

public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumExtension
public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumHessianBound
public import ReasLib.Analysis.Convex.HessianPerturbation.Bounds

public section

open Filter Set Topology

universe u

namespace DisjointFinsum

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A twice differentiable zero extension of a disjoint shrinking finsum with a supportwise
Hessian bound gives two-sided global Hessian bounds after adding a quadratic base. -/
theorem hasHessianBounds_indicator_compl_finsum_add_halfNormSq_of_decay
    (C : E) (Gamma : Set E) (x : ℕ → E) (rho : ℕ → ℝ) (psi : ℕ → E → ℝ)
    (eta : ℝ) (heta : 0 ≤ eta) (hGamma : IsClosed Gamma)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Gamma)
    (hrho : ∀ k, 0 ≤ rho k) (hrho0 : Tendsto rho atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (rho k)))
    (hsupport : ∀ k, tsupport (psi k) ⊆ Metric.closedBall (x k) (rho k))
    (hsmooth : ∀ k, ContDiff ℝ 2 (psi k))
    (hbound : ∀ k z, z ∈ tsupport (psi k) →
      ‖fderiv ℝ (fderiv ℝ (psi k)) z‖ ≤ eta)
    (hvalue : Tendsto (fun z ↦ ‖∑ᶠ k, psi k z‖ / Metric.infDist z Gamma ^ 2)
      (comap (fun z ↦ Metric.infDist z Gamma) (𝓝 0) ⊓ principal Gammaᶜ) (𝓝 0))
    (hderiv : Tendsto (fun z ↦ ‖fderiv ℝ (fun w ↦ ∑ᶠ k, psi k w) z‖ /
        Metric.infDist z Gamma)
      (comap (fun z ↦ Metric.infDist z Gamma) (𝓝 0) ⊓ principal Gammaᶜ) (𝓝 0))
    (hsecond : Tendsto
      (fun z ↦ ‖fderiv ℝ (fderiv ℝ (fun w ↦ ∑ᶠ k, psi k w)) z‖)
      (comap (fun z ↦ Metric.infDist z Gamma) (𝓝 0) ⊓ principal Gammaᶜ) (𝓝 0)) :
    HasHessianBounds (1 - eta) (1 + eta)
      (fun y ↦ (1 / 2 : ℝ) * ‖y - C‖ ^ 2 +
        Gammaᶜ.indicator (fun w ↦ ∑ᶠ k, psi k w) y) := by
  have hPsi : ContDiff ℝ 2
      (Gammaᶜ.indicator (fun w ↦ ∑ᶠ k, psi k w)) :=
    contDiff_two_indicator_compl_finsum_of_decay Gamma x rho psi hGamma hcluster hrho hrho0
      hballs hsupport hsmooth hvalue hderiv hsecond
  apply HessianPerturbation.hasHessianBounds_halfNormSq_sub_add_of_secondFDeriv_norm_le
    C (Gammaᶜ.indicator (fun w ↦ ∑ᶠ k, psi k w)) eta hPsi
  intro y
  exact norm_secondFDeriv_indicator_compl_finsum_le_of_tsupport_bound
    Gamma x rho psi eta heta hGamma hcluster hrho hrho0 hballs hsupport hsmooth hbound
      hvalue hderiv y

end DisjointFinsum
