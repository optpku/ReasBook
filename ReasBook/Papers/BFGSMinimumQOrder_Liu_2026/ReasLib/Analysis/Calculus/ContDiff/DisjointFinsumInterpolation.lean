module

public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumJets
public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

open Filter Set Topology

universe u v

namespace DisjointFinsum

/-- The value of a pointwise disjoint finsum at an active center is the value of its unique
active summand. -/
theorem value_eq_at_center
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F)
    (hΓ : IsClosed Γ) (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k)) (k : ℕ) (hxk : x k ∈ Γᶜ)
    (hcenter : x k ∈ tsupport (ψ k)) :
    (∑ᶠ n, ψ n (x k)) = ψ k (x k) := by
  have hjet := iteratedFDeriv_finsum_eq_at_center m Γ x ρ ψ hΓ hcluster hρ hρ0
    hballs hsupport hsmooth k 0 hxk hcenter (Nat.zero_le m)
  simpa only [iteratedFDeriv_zero_apply] using
    congrArg (fun L ↦ L (fun _ ↦ 0)) hjet

/-- At an active center outside the cluster set, the ordinary Fréchet derivative of a
pointwise disjoint finsum is the derivative of the unique active summand. -/
theorem fderiv_eq_at_center
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F)
    (hΓ : IsClosed Γ) (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k)) (k : ℕ) (hxk : x k ∈ Γᶜ)
    (hcenter : x k ∈ tsupport (ψ k)) (hm : 1 ≤ m) :
    fderiv ℝ (fun w ↦ ∑ᶠ n, ψ n w) (x k) = fderiv ℝ (ψ k) (x k) := by
  have hjet := iteratedFDeriv_finsum_eq_at_center m Γ x ρ ψ hΓ hcluster hρ hρ0
    hballs hsupport hsmooth k 1 hxk hcenter hm
  ext z
  simpa only [iteratedFDeriv_one_apply] using congrArg (fun L ↦ L (fun _ ↦ z)) hjet

/-- A gradient certificate for an active summand transfers to the pointwise disjoint finsum
at the same center. -/
theorem hasGradientAt_at_center
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (m : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → ℝ)
    (hΓ : IsClosed Γ) (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k)) (k : ℕ) (hxk : x k ∈ Γᶜ)
    (hcenter : x k ∈ tsupport (ψ k)) (hm : 1 ≤ m)
    {g : E} (hgradient : HasGradientAt (ψ k) g (x k)) :
    HasGradientAt (fun w ↦ ∑ᶠ n, ψ n w) g (x k) := by
  have hmCast : (1 : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hm
  have hsmoothOne : ∀ n, ContDiff ℝ 1 (ψ n) := fun n ↦ (hsmooth n).of_le hmCast
  have houtside : ContDiffOn ℝ 1 (fun w ↦ ∑ᶠ n, ψ n w) Γᶜ :=
    contDiffOn_finsum_outside 1 Γ x ρ ψ hΓ hcluster hρ0 hsupport hsmoothOne
  have hone_ne : (1 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hdiffOn : DifferentiableOn ℝ (fun w ↦ ∑ᶠ n, ψ n w) Γᶜ :=
    houtside.differentiableOn hone_ne
  have hxnot : x k ∉ Γ := by
    simpa only [mem_compl_iff] using hxk
  have hnhds : Γᶜ ∈ 𝓝 (x k) := hΓ.compl_mem_nhds hxnot
  have hdiff : DifferentiableAt ℝ (fun w ↦ ∑ᶠ n, ψ n w) (x k) :=
    (hdiffOn (x k) hxk).differentiableAt hnhds
  have hderiv : fderiv ℝ (fun w ↦ ∑ᶠ n, ψ n w) (x k) =
      (InnerProductSpace.toDual ℝ E) g := by
    rw [fderiv_eq_at_center m Γ x ρ ψ hΓ hcluster hρ hρ0 hballs hsupport hsmooth k hxk
      hcenter hm, hgradient.hasFDerivAt.fderiv]
  have hsum : HasFDerivAt (fun w ↦ ∑ᶠ n, ψ n w)
      ((InnerProductSpace.toDual ℝ E) g) (x k) := by
    rw [← hderiv]
    exact hdiff.hasFDerivAt
  simpa using hsum.hasGradientAt

/-- The gradient of a pointwise disjoint finsum at an active center is the certified gradient
of its active summand. -/
theorem gradient_at_center
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (m : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → ℝ)
    (hΓ : IsClosed Γ) (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k)) (k : ℕ) (hxk : x k ∈ Γᶜ)
    (hcenter : x k ∈ tsupport (ψ k)) (hm : 1 ≤ m)
    {g : E} (hgradient : HasGradientAt (ψ k) g (x k)) :
    gradient (fun w ↦ ∑ᶠ n, ψ n w) (x k) = g := by
  exact (hasGradientAt_at_center m Γ x ρ ψ hΓ hcluster hρ hρ0 hballs hsupport hsmooth
    k hxk hcenter hm hgradient).gradient

end DisjointFinsum
