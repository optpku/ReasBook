module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Field.Basic

public section

open Filter
open scoped Topology

universe u v w

namespace LocalCutoff.GraphTransform.UniformRemainder

/-- Infrastructure I.16a: a residual decomposition with independent uniform bounds
on its principal and remainder terms. -/
structure ResidualNormCertificate (α : Type u) (Y : Type v)
    [NormedAddCommGroup Y] where
  residual : α → Y
  principal : α → Y
  remainder : α → Y
  decomposition : ∀ x, residual x = principal x + remainder x
  principalBound : ℝ
  remainderBound : ℝ
  principal_norm_le : ∀ x, ‖principal x‖ ≤ principalBound
  remainder_norm_le : ∀ x, ‖remainder x‖ ≤ remainderBound

/-- Infrastructure I.16a: the residual norm is bounded by the sum of the two
certificate bounds. -/
theorem ResidualNormCertificate.residual_norm_le
    {α : Type u} {Y : Type v} [NormedAddCommGroup Y]
    (certificate : ResidualNormCertificate α Y) (x : α) :
    ‖certificate.residual x‖ ≤
      certificate.principalBound + certificate.remainderBound := by
  rw [certificate.decomposition]
  exact (norm_add_le _ _).trans
    (add_le_add (certificate.principal_norm_le x) (certificate.remainder_norm_le x))

/-- Infrastructure I.16a: a finite family of branchwise bounds gives a bound
for the non-distinguished branch sum at one parameter. -/
theorem finiteNonDistinguishedSum_norm_le
    {α : Type u} {Y : Type v} [Fintype α] [DecidableEq α]
    [NormedAddCommGroup Y]
    (distinguished : α) (b : α → Y) (C : α → ℝ)
    (hbranch : ∀ c, c ≠ distinguished → ‖b c‖ ≤ C c) :
    ‖∑ c : α, if c = distinguished then 0 else b c‖ ≤
      ∑ c : α, if c = distinguished then 0 else C c := by
  classical
  calc
    ‖∑ c : α, if c = distinguished then 0 else b c‖ ≤
        ∑ c : α, ‖if c = distinguished then 0 else b c‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : α, (if c = distinguished then 0 else C c) := by
      apply Finset.sum_le_sum
      intro c hc
      by_cases hcd : c = distinguished
      · simp [hcd]
      · simpa [hcd] using hbranch c hcd

/-- Infrastructure I.16a: finite branchwise compact-uniform bounds admit one
common radius and a uniform bound for the non-distinguished branch sum. -/
theorem finiteNonDistinguishedSum_uniformBoundOn
    {α : Type u} {Θ : Type v} {Y : Type w}
    [Fintype α] [DecidableEq α] [NormedAddCommGroup Y]
    (distinguished : α) (K : Set Θ) (b : α → Θ → ℝ → Y) (C : α → ℝ)
    (hbranch : ∀ c, c ≠ distinguished → ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
      ‖t‖ < δ → ‖b c u t‖ ≤ C c * ‖t‖) :
    ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ, ‖t‖ < δ →
      ‖∑ c : α, if c = distinguished then 0 else b c u t‖ ≤
        (∑ c : α, if c = distinguished then 0 else C c) * ‖t‖ := by
  classical
  have hbranch_eventually (c : α) (hc : c ≠ distinguished) :
      ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u ∈ K, ‖b c u t‖ ≤ C c * ‖t‖ := by
    obtain ⟨δ, hδ, hδ_spec⟩ := hbranch c hc
    rw [Metric.eventually_nhds_iff]
    refine ⟨δ, hδ, ?_⟩
    intro t ht u hu
    have hnorm : ‖t‖ < δ := by
      simpa only [dist_zero_right] using ht
    exact hδ_spec u hu t hnorm
  have hbranch_eventually' (c : α) :
      ∀ᶠ t in 𝓝 (0 : ℝ), c ≠ distinguished →
        ∀ u ∈ K, ‖b c u t‖ ≤ C c * ‖t‖ := by
    by_cases hc : c = distinguished
    · filter_upwards [] with t hct
      exact (hct hc).elim
    · simpa [hc] using hbranch_eventually c hc
  have hAll : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ c, c ≠ distinguished →
      ∀ u ∈ K, ‖b c u t‖ ≤ C c * ‖t‖ :=
    (Filter.eventually_all).mpr hbranch_eventually'
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.eventually_nhds_iff.mp hAll
  refine ⟨δ, hδ, ?_⟩
  intro u hu t ht
  have hbranches : ∀ c, c ≠ distinguished →
      ‖b c u t‖ ≤ C c * ‖t‖ := by
    intro c hc
    have hdist : dist t 0 < δ := by
      simpa only [dist_zero_right] using ht
    exact hδ_spec hdist c hc u hu
  calc
    ‖∑ c : α, if c = distinguished then 0 else b c u t‖ ≤
        ∑ c : α, ‖if c = distinguished then 0 else b c u t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : α, (if c = distinguished then 0 else C c) * ‖t‖ := by
      apply Finset.sum_le_sum
      intro c hc
      by_cases hcd : c = distinguished
      · simp [hcd]
      · simpa [hcd] using hbranches c hcd
    _ = (∑ c : α, if c = distinguished then 0 else C c) * ‖t‖ := by
      rw [Finset.sum_mul]

end LocalCutoff.GraphTransform.UniformRemainder
