module

public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumDecay
public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumExtension

public section

open Filter Topology

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Supportwise quadratic, linear, and zeroth-order decay of the first three jets of
disjoint shrinking summands makes their zero extension twice continuously differentiable. -/
theorem contDiff_two_indicator_compl_finsum_of_supportwise_decay
    (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F) (hΓ : IsClosed Γ)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ) (hρ : ∀ k, 0 ≤ ρ k)
    (hρ0 : Tendsto ρ atTop (nhds 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ 2 (ψ k))
    (hvalueDecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖ψ k z‖ / Metric.infDist z Γ ^ 2 < η)
    (hderivDecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖fderiv ℝ (ψ k) z‖ / Metric.infDist z Γ < η)
    (hsecondDecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖fderiv ℝ (fderiv ℝ (ψ k)) z‖ < η) :
    ContDiff ℝ 2 (Γᶜ.indicator fun z ↦ ∑ᶠ k, ψ k z) := by
  have hj0 : 0 ≤ 2 := Nat.zero_le 2
  have hj1 : 1 ≤ 2 := by omega
  have hj2 : 2 ≤ 2 := le_rfl
  have hsecondNorm : ∀ (f : E → F) z,
      ‖fderiv ℝ (fderiv ℝ f) z‖ = ‖iteratedFDeriv ℝ 2 f z‖ := by
    intro f z
    calc
      ‖fderiv ℝ (fderiv ℝ f) z‖ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ f) z‖ :=
        (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ f)).symm
      _ = ‖iteratedFDeriv ℝ 2 f z‖ :=
        norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (n := 1)
  have hdecay0 : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖iteratedFDeriv ℝ 0 (ψ k) z‖ / Metric.infDist z Γ ^ 2 < η := by
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hvalueDecay η hη
    refine ⟨δ, hδ, ?_⟩
    intro k z hzΓ hzk hzδ
    simpa only [norm_iteratedFDeriv_zero] using hbound k z hzΓ hzk hzδ
  have hdecay1 : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖iteratedFDeriv ℝ 1 (ψ k) z‖ / Metric.infDist z Γ ^ 1 < η := by
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hderivDecay η hη
    refine ⟨δ, hδ, ?_⟩
    intro k z hzΓ hzk hzδ
    simpa only [norm_iteratedFDeriv_one, pow_one] using hbound k z hzΓ hzk hzδ
  have hdecay2 : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖iteratedFDeriv ℝ 2 (ψ k) z‖ / Metric.infDist z Γ ^ 0 < η := by
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hsecondDecay η hη
    refine ⟨δ, hδ, ?_⟩
    intro k z hzΓ hzk hzδ
    rw [pow_zero, div_one, ← hsecondNorm (ψ k) z]
    exact hbound k z hzΓ hzk hzδ
  have hvalueIterated := tendsto_norm_iteratedFDeriv_finsum_div_infDist_pow
    2 0 2 Γ x ρ ψ hΓ hcluster hρ hρ0 hballs hsupport hsmooth hj0 hdecay0
  have hderivIterated := tendsto_norm_iteratedFDeriv_finsum_div_infDist_pow
    2 1 1 Γ x ρ ψ hΓ hcluster hρ hρ0 hballs hsupport hsmooth hj1 hdecay1
  have hsecondIterated := tendsto_norm_iteratedFDeriv_finsum_div_infDist_pow
    2 2 0 Γ x ρ ψ hΓ hcluster hρ hρ0 hballs hsupport hsmooth hj2 hdecay2
  have hvalue : Tendsto (fun z ↦ ‖∑ᶠ k, ψ k z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (nhds 0) ⊓ Filter.principal Γᶜ)
      (nhds 0) := by
    simpa only [norm_iteratedFDeriv_zero] using hvalueIterated
  have hderiv : Tendsto (fun z ↦ ‖fderiv ℝ (fun w ↦ ∑ᶠ k, ψ k w) z‖ /
      Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (nhds 0) ⊓ Filter.principal Γᶜ)
      (nhds 0) := by
    simpa only [norm_iteratedFDeriv_one, pow_one] using hderivIterated
  have hsecond : Tendsto
      (fun z ↦ ‖fderiv ℝ (fderiv ℝ (fun w ↦ ∑ᶠ k, ψ k w)) z‖)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (nhds 0) ⊓ Filter.principal Γᶜ)
      (nhds 0) := by
    simpa only [pow_zero, div_one, ← hsecondNorm] using hsecondIterated
  exact contDiff_two_indicator_compl_finsum_of_decay Γ x ρ ψ hΓ hcluster hρ hρ0 hballs
    hsupport hsmooth hvalue hderiv hsecond
