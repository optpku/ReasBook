module

public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumCenterInterpolation
public import ReasLib.Analysis.Calculus.ContDiff.ZeroExtensionJets.Outside
public import ReasLib.Analysis.Convex.HessianPerturbation.Interpolation

public section

open Filter Set Topology

universe u

namespace DisjointFinsum

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If the centered summand vanishes at its center, adding the pointwise disjoint finsum
does not change the translated quadratic value there. -/
theorem halfNormSq_sub_add_finsum_apply_center_of_disjoint
    (C : E) (m : ℕ) (Gamma : Set E) (x : ℕ → E) (rho : ℕ → ℝ)
    (psi : ℕ → E → ℝ) (hGamma : IsClosed Gamma)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Gamma)
    (hrho : ∀ k, 0 ≤ rho k) (hrho0 : Tendsto rho atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (rho k)))
    (hsupport : ∀ k, tsupport (psi k) ⊆ Metric.closedBall (x k) (rho k))
    (hsmooth : ∀ k, ContDiff ℝ m (psi k)) (k : ℕ) (hxk : x k ∈ Gammaᶜ)
    (hzero : psi k (x k) = 0) :
    (1 / 2 : ℝ) * ‖x k - C‖ ^ 2 + (∑ᶠ n, psi n (x k)) =
      (1 / 2 : ℝ) * ‖x k - C‖ ^ 2 := by
  apply HessianPerturbation.halfNormSq_sub_add_apply_of_eq_zero
    C (Ψ := fun y ↦ ∑ᶠ n, psi n y) (x := x k)
  rw [value_eq_at_center_of_disjoint m Gamma x rho psi hGamma hcluster hrho hrho0
    hballs hsupport hsmooth k hxk]
  exact hzero

/-- A centered-summand gradient certificate gives the corresponding gradient certificate
for a translated quadratic plus the pointwise disjoint finsum. -/
theorem hasGradientAt_halfNormSq_sub_add_finsum_center_of_disjoint
    [CompleteSpace E] (C : E) (m : ℕ) (Gamma : Set E) (x : ℕ → E)
    (rho : ℕ → ℝ) (psi : ℕ → E → ℝ) (hGamma : IsClosed Gamma)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Gamma)
    (hrho : ∀ k, 0 ≤ rho k) (hrho0 : Tendsto rho atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (rho k)))
    (hsupport : ∀ k, tsupport (psi k) ⊆ Metric.closedBall (x k) (rho k))
    (hsmooth : ∀ k, ContDiff ℝ m (psi k)) (k : ℕ) (hxk : x k ∈ Gammaᶜ)
    (hm : 1 ≤ m) {g : E} (hgradient : HasGradientAt (psi k) g (x k)) :
    HasGradientAt
      (fun y ↦ (1 / 2 : ℝ) * ‖y - C‖ ^ 2 + ∑ᶠ n, psi n y)
      (x k - C + g) (x k) := by
  apply HessianPerturbation.hasGradientAt_halfNormSq_sub_add C
  exact hasGradientAt_at_center_of_disjoint m Gamma x rho psi hGamma hcluster hrho hrho0
    hballs hsupport hsmooth k hxk hm hgradient

/-- The gradient of a translated quadratic plus a pointwise disjoint finsum at a center is
the displacement from the quadratic center plus the centered-summand gradient. -/
theorem gradient_halfNormSq_sub_add_finsum_center_of_disjoint
    [CompleteSpace E] (C : E) (m : ℕ) (Gamma : Set E) (x : ℕ → E)
    (rho : ℕ → ℝ) (psi : ℕ → E → ℝ) (hGamma : IsClosed Gamma)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Gamma)
    (hrho : ∀ k, 0 ≤ rho k) (hrho0 : Tendsto rho atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (rho k)))
    (hsupport : ∀ k, tsupport (psi k) ⊆ Metric.closedBall (x k) (rho k))
    (hsmooth : ∀ k, ContDiff ℝ m (psi k)) (k : ℕ) (hxk : x k ∈ Gammaᶜ)
    (hm : 1 ≤ m) {g : E} (hgradient : HasGradientAt (psi k) g (x k)) :
    gradient (fun y ↦ (1 / 2 : ℝ) * ‖y - C‖ ^ 2 + ∑ᶠ n, psi n y) (x k) =
      x k - C + g := by
  exact (hasGradientAt_halfNormSq_sub_add_finsum_center_of_disjoint
    C m Gamma x rho psi hGamma hcluster hrho hrho0 hballs hsupport hsmooth k hxk hm
      hgradient).gradient

/-- At a designated center outside the cluster set, the zero extension of a pointwise
disjoint finsum has the value of the centered summand. -/
theorem value_indicator_compl_finsum_eq_at_center_of_disjoint
    (m : ℕ) (Gamma : Set E) (x : ℕ → E) (rho : ℕ → ℝ) (psi : ℕ → E → ℝ)
    (hGamma : IsClosed Gamma) (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Gamma)
    (hrho : ∀ k, 0 ≤ rho k) (hrho0 : Tendsto rho atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (rho k)))
    (hsupport : ∀ k, tsupport (psi k) ⊆ Metric.closedBall (x k) (rho k))
    (hsmooth : ∀ k, ContDiff ℝ m (psi k)) (k : ℕ) (hxk : x k ∈ Gammaᶜ) :
    Gammaᶜ.indicator (fun w ↦ ∑ᶠ n, psi n w) (x k) = psi k (x k) := by
  rw [indicator_of_mem hxk]
  exact value_eq_at_center_of_disjoint m Gamma x rho psi hGamma hcluster hrho hrho0
    hballs hsupport hsmooth k hxk

/-- A gradient certificate for a centered summand transfers to the zero extension of the
pointwise disjoint finsum at that center. -/
theorem hasGradientAt_indicator_compl_finsum_at_center_of_disjoint
    [CompleteSpace E]
    (m : ℕ) (Gamma : Set E) (x : ℕ → E) (rho : ℕ → ℝ) (psi : ℕ → E → ℝ)
    (hGamma : IsClosed Gamma) (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Gamma)
    (hrho : ∀ k, 0 ≤ rho k) (hrho0 : Tendsto rho atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (rho k)))
    (hsupport : ∀ k, tsupport (psi k) ⊆ Metric.closedBall (x k) (rho k))
    (hsmooth : ∀ k, ContDiff ℝ m (psi k)) (k : ℕ) (hxk : x k ∈ Gammaᶜ)
    (hm : 1 ≤ m) {g : E} (hgradient : HasGradientAt (psi k) g (x k)) :
    HasGradientAt (Gammaᶜ.indicator (fun w ↦ ∑ᶠ n, psi n w)) g (x k) := by
  have hsum : HasGradientAt (fun w ↦ ∑ᶠ n, psi n w) g (x k) :=
    hasGradientAt_at_center_of_disjoint m Gamma x rho psi hGamma hcluster hrho hrho0
      hballs hsupport hsmooth k hxk hm hgradient
  exact hsum.indicator_compl_of_mem hGamma hxk

/-- If the centered summand vanishes at its center, adding the zero-extended disjoint finsum
does not change the translated quadratic value there. -/
theorem halfNormSq_sub_add_indicator_compl_finsum_apply_center
    (C : E) (m : ℕ) (Gamma : Set E) (x : ℕ → E) (rho : ℕ → ℝ)
    (psi : ℕ → E → ℝ) (hGamma : IsClosed Gamma)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Gamma)
    (hrho : ∀ k, 0 ≤ rho k) (hrho0 : Tendsto rho atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (rho k)))
    (hsupport : ∀ k, tsupport (psi k) ⊆ Metric.closedBall (x k) (rho k))
    (hsmooth : ∀ k, ContDiff ℝ m (psi k)) (k : ℕ) (hxk : x k ∈ Gammaᶜ)
    (hzero : psi k (x k) = 0) :
    (1 / 2 : ℝ) * ‖x k - C‖ ^ 2 +
        Gammaᶜ.indicator (fun w ↦ ∑ᶠ n, psi n w) (x k) =
      (1 / 2 : ℝ) * ‖x k - C‖ ^ 2 := by
  apply HessianPerturbation.halfNormSq_sub_add_apply_of_eq_zero C
  rw [value_indicator_compl_finsum_eq_at_center_of_disjoint m Gamma x rho psi hGamma
    hcluster hrho hrho0 hballs hsupport hsmooth k hxk]
  exact hzero

/-- A centered-summand gradient certificate gives the corresponding gradient certificate
for a translated quadratic plus the zero-extended disjoint finsum. -/
theorem hasGradientAt_halfNormSq_sub_add_indicator_compl_finsum_center
    [CompleteSpace E]
    (C : E) (m : ℕ) (Gamma : Set E) (x : ℕ → E) (rho : ℕ → ℝ)
    (psi : ℕ → E → ℝ) (hGamma : IsClosed Gamma)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Gamma)
    (hrho : ∀ k, 0 ≤ rho k) (hrho0 : Tendsto rho atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (rho k)))
    (hsupport : ∀ k, tsupport (psi k) ⊆ Metric.closedBall (x k) (rho k))
    (hsmooth : ∀ k, ContDiff ℝ m (psi k)) (k : ℕ) (hxk : x k ∈ Gammaᶜ)
    (hm : 1 ≤ m) {g : E} (hgradient : HasGradientAt (psi k) g (x k)) :
    HasGradientAt
      (fun y ↦ (1 / 2 : ℝ) * ‖y - C‖ ^ 2 +
        Gammaᶜ.indicator (fun w ↦ ∑ᶠ n, psi n w) y)
      (x k - C + g) (x k) := by
  apply HessianPerturbation.hasGradientAt_halfNormSq_sub_add C
  exact hasGradientAt_indicator_compl_finsum_at_center_of_disjoint
    m Gamma x rho psi hGamma hcluster hrho hrho0 hballs hsupport hsmooth k hxk hm hgradient

/-- The gradient of a translated quadratic plus a zero-extended disjoint finsum at a center
is the displacement from the quadratic center plus the centered-summand gradient. -/
theorem gradient_halfNormSq_sub_add_indicator_compl_finsum_center
    [CompleteSpace E]
    (C : E) (m : ℕ) (Gamma : Set E) (x : ℕ → E) (rho : ℕ → ℝ)
    (psi : ℕ → E → ℝ) (hGamma : IsClosed Gamma)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Gamma)
    (hrho : ∀ k, 0 ≤ rho k) (hrho0 : Tendsto rho atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (rho k)))
    (hsupport : ∀ k, tsupport (psi k) ⊆ Metric.closedBall (x k) (rho k))
    (hsmooth : ∀ k, ContDiff ℝ m (psi k)) (k : ℕ) (hxk : x k ∈ Gammaᶜ)
    (hm : 1 ≤ m) {g : E} (hgradient : HasGradientAt (psi k) g (x k)) :
    gradient
      (fun y ↦ (1 / 2 : ℝ) * ‖y - C‖ ^ 2 +
        Gammaᶜ.indicator (fun w ↦ ∑ᶠ n, psi n w) y)
      (x k) = x k - C + g := by
  exact (hasGradientAt_halfNormSq_sub_add_indicator_compl_finsum_center
    C m Gamma x rho psi hGamma hcluster hrho hrho0 hballs hsupport hsmooth k hxk hm
      hgradient).gradient

end DisjointFinsum
