module

public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumInterpolation
public import ReasLib.Analysis.Calculus.ContDiff.SupportBounds

public section

open Filter Set Topology

universe u v

namespace DisjointFinsum

/-- At a designated center outside the cluster set, every available iterated derivative
of a pointwise disjoint finsum equals that of the corresponding summand. No assumption
that the center belongs to the summand's topological support is needed. -/
theorem iteratedFDeriv_finsum_eq_centered
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F)
    (hΓ : IsClosed Γ) (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k)) (k j : ℕ) (hxk : x k ∈ Γᶜ)
    (hj : j ≤ m) :
    iteratedFDeriv ℝ j (fun w ↦ ∑ᶠ n, ψ n w) (x k) =
      iteratedFDeriv ℝ j (ψ k) (x k) := by
  by_cases hcenter : x k ∈ tsupport (ψ k)
  · exact iteratedFDeriv_finsum_eq_at_center m Γ x ρ ψ hΓ hcluster hρ hρ0
      hballs hsupport hsmooth k j hxk hcenter hj
  · have hxball : x k ∈ Metric.closedBall (x k) (ρ k) := by
      simpa only [Metric.mem_closedBall, dist_self] using hρ k
    have hallInactive : ∀ n, x k ∉ tsupport (ψ n) := by
      intro n hn
      by_cases hnk : n = k
      · subst n
        exact hcenter hn
      · have hnkEq : n = k :=
          hballs.elim_set (Set.mem_univ n) (Set.mem_univ k) (x k)
            (hsupport n hn) hxball
        exact hnk hnkEq
    have hsumZero := iteratedFDeriv_finsum_eq_zero Γ x ρ ψ hcluster hρ0 hsupport hxk
      (j := j) hallInactive
    have hsummandZero := iteratedFDeriv_eq_zero_of_notMem_tsupport
      (𝕜 := ℝ) (ψ k) j hcenter
    rw [hsumZero, hsummandZero]

/-- The value of a pointwise disjoint finsum at a designated center equals the value of
the centered summand, including when both sides vanish near that center. -/
theorem value_eq_at_center_of_disjoint
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F)
    (hΓ : IsClosed Γ) (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k)) (k : ℕ) (hxk : x k ∈ Γᶜ) :
    (∑ᶠ n, ψ n (x k)) = ψ k (x k) := by
  have hjet := iteratedFDeriv_finsum_eq_centered m Γ x ρ ψ hΓ hcluster hρ hρ0
    hballs hsupport hsmooth k 0 hxk (Nat.zero_le m)
  simpa only [iteratedFDeriv_zero_apply] using
    congrArg (fun L ↦ L (fun _ ↦ 0)) hjet

/-- The first Frechet derivative of a pointwise disjoint finsum at a designated center
equals that of the centered summand without an active-support assumption. -/
theorem fderiv_eq_at_center_of_disjoint
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F)
    (hΓ : IsClosed Γ) (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k)) (k : ℕ) (hxk : x k ∈ Γᶜ)
    (hm : 1 ≤ m) :
    fderiv ℝ (fun w ↦ ∑ᶠ n, ψ n w) (x k) = fderiv ℝ (ψ k) (x k) := by
  have hjet := iteratedFDeriv_finsum_eq_centered m Γ x ρ ψ hΓ hcluster hρ hρ0
    hballs hsupport hsmooth k 1 hxk hm
  ext z
  simpa only [iteratedFDeriv_one_apply] using
    congrArg (fun L ↦ L (fun _ ↦ z)) hjet

/-- A gradient certificate for the centered summand transfers to the pointwise disjoint
finsum even when the center is outside every topological support. -/
theorem hasGradientAt_at_center_of_disjoint
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (m : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → ℝ)
    (hΓ : IsClosed Γ) (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k)) (k : ℕ) (hxk : x k ∈ Γᶜ)
    (hm : 1 ≤ m) {g : E} (hgradient : HasGradientAt (ψ k) g (x k)) :
    HasGradientAt (fun w ↦ ∑ᶠ n, ψ n w) g (x k) := by
  have hmCast : (1 : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hm
  have hsmoothOne : ∀ n, ContDiff ℝ 1 (ψ n) :=
    fun n ↦ (hsmooth n).of_le hmCast
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
    rw [fderiv_eq_at_center_of_disjoint m Γ x ρ ψ hΓ hcluster hρ hρ0 hballs
      hsupport hsmooth k hxk hm, hgradient.hasFDerivAt.fderiv]
  have hsum : HasFDerivAt (fun w ↦ ∑ᶠ n, ψ n w)
      ((InnerProductSpace.toDual ℝ E) g) (x k) := by
    rw [← hderiv]
    exact hdiff.hasFDerivAt
  simpa using hsum.hasGradientAt

/-- The gradient of a pointwise disjoint finsum at a designated center is the certified
gradient of the centered summand, without requiring active support at the center. -/
theorem gradient_at_center_of_disjoint
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (m : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → ℝ)
    (hΓ : IsClosed Γ) (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k)) (k : ℕ) (hxk : x k ∈ Γᶜ)
    (hm : 1 ≤ m) {g : E} (hgradient : HasGradientAt (ψ k) g (x k)) :
    gradient (fun w ↦ ∑ᶠ n, ψ n w) (x k) = g := by
  exact (hasGradientAt_at_center_of_disjoint m Γ x ρ ψ hΓ hcluster hρ hρ0 hballs
    hsupport hsmooth k hxk hm hgradient).gradient

end DisjointFinsum
