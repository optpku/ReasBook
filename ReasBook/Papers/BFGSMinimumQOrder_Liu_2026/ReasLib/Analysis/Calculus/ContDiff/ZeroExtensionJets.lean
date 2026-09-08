module

public import ReasLib.Analysis.Calculus.ContDiff.ZeroExtension
public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

open Filter Set Topology

universe u v

namespace IsClosed

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A zero extension has vanishing first derivative at every point of the closed set
when the source function has the distance-scaled value decay required for extension. -/
theorem fderiv_indicator_compl_eq_zero_of_mem
    (Γ : Set E) (Ψ : E → F) (hΓ : IsClosed Γ)
    (hΨ : DifferentiableOn ℝ Ψ Γᶜ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0))
    {x : E} (hx : x ∈ Γ) :
    fderiv ℝ (Γᶜ.indicator Ψ) x = 0 := by
  have hxcompl : x ∉ Γᶜ := by
    simpa only [mem_compl_iff, not_not] using hx
  rw [fderiv_indicator_compl Γ Ψ hΓ hΨ hvalue]
  exact indicator_of_notMem hxcompl _

/-- A zero extension has zero Euclidean gradient at every point of the closed set under the
same first-order value decay hypothesis. -/
theorem gradient_indicator_compl_eq_zero_of_mem
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Γ : Set E) (Ψ : E → ℝ) (hΓ : IsClosed Γ)
    (hΨ : DifferentiableOn ℝ Ψ Γᶜ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0))
    {x : E} (hx : x ∈ Γ) :
    gradient (Γᶜ.indicator Ψ) x = 0 := by
  rw [gradient, fderiv_indicator_compl_eq_zero_of_mem Γ Ψ hΓ hΨ hvalue hx]
  simp

/-- A zero extension has vanishing second Fréchet derivative at every point of the closed
set when the source value and first derivative satisfy the second-order extension decay. -/
theorem fderiv_fderiv_indicator_compl_eq_zero_of_mem
    (Γ : Set E) (Ψ : E → F) (hΓ : IsClosed Γ)
    (hΨ : ContDiffOn ℝ 2 Ψ Γᶜ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0))
    (hderiv : Tendsto (fun z ↦ ‖fderiv ℝ Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0))
    {x : E} (hx : x ∈ Γ) :
    fderiv ℝ (fderiv ℝ (Γᶜ.indicator Ψ)) x = 0 := by
  have hxcompl : x ∉ Γᶜ := by
    simpa only [mem_compl_iff, not_not] using hx
  rw [fderiv_fderiv_indicator_compl Γ Ψ hΓ hΨ hvalue hderiv]
  exact indicator_of_notMem hxcompl _

end IsClosed
