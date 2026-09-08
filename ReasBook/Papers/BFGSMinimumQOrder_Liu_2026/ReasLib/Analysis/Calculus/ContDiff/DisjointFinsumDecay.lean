module

public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumBounds

public section

open Filter Topology

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A supportwise scaled decay estimate for disjoint shrinking summands gives the
same decay for their pointwise finsum along the complement of the cluster set. -/
theorem tendsto_norm_iteratedFDeriv_finsum_div_infDist_pow
    (m j q : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F)
    (hΓ : IsClosed Γ) (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ : ∀ k, 0 ≤ ρ k) (hρ0 : Tendsto ρ atTop (nhds 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k)) (hj : j ≤ m)
    (hdecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖iteratedFDeriv ℝ j (ψ k) z‖ / Metric.infDist z Γ ^ q < η) :
    Tendsto
      (fun z ↦ ‖iteratedFDeriv ℝ j (fun w ↦ ∑ᶠ n, ψ n w) z‖ /
        Metric.infDist z Γ ^ q)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (nhds 0) ⊓ Filter.principal Γᶜ)
      (nhds 0) := by
  refine Metric.tendsto_nhds.mpr ?_
  intro η hη
  obtain ⟨δ, hδ, hdecayδ⟩ := hdecay η hη
  have hnearReal : ∀ᶠ r : ℝ in nhds 0, r < δ := Iio_mem_nhds hδ
  have hnear : ∀ᶠ z : E in Filter.comap (fun z ↦ Metric.infDist z Γ) (nhds 0),
      Metric.infDist z Γ < δ :=
    hnearReal.comap (fun z ↦ Metric.infDist z Γ)
  refine eventually_inf_principal.mpr ?_
  filter_upwards [hnear] with z hzδ
  intro hzΓ
  by_cases hactive : ∃ k, z ∈ tsupport (ψ k)
  · obtain ⟨k, hzk⟩ := hactive
    have hfinsum := iteratedFDeriv_finsum_eq_of_mem_tsupport Γ x ρ ψ hcluster hρ0 hballs
      hsupport hzΓ (k := k) (j := j) hzk
    have hbound := hdecayδ k z hzΓ hzk hzδ
    have hdenom : 0 ≤ Metric.infDist z Γ ^ q :=
      pow_nonneg Metric.infDist_nonneg q
    have hquotient : 0 ≤ ‖iteratedFDeriv ℝ j (ψ k) z‖ / Metric.infDist z Γ ^ q :=
      div_nonneg (norm_nonneg _) hdenom
    rw [hfinsum, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hquotient]
    exact hbound
  · have hfinsum := iteratedFDeriv_finsum_eq_zero Γ x ρ ψ hcluster hρ0 hsupport hzΓ
      (j := j) (not_exists.mp hactive)
    rw [hfinsum, norm_zero, zero_div, dist_self]
    exact hη
