module

public import ReasLib.Analysis.Calculus.ContDiff.EuclideanPlaneZeroExtensionJets

public section

open Filter Set Topology

universe u v

namespace Filter

variable {E : Type u} {F : Type v}
  [PseudoMetricSpace E] [SeminormedAddCommGroup F]

/-- Quadratic decay relative to the distance from a set implies the corresponding
first-order decay along the same distance filter. -/
theorem tendsto_norm_div_infDist_of_sq
    (Γ : Set E) (Ψ : E → F)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0)) :
    Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0) := by
  have hinfDist : Tendsto (fun z ↦ Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0) := tendsto_inf_left tendsto_comap
  have hproduct : Tendsto
      (fun z ↦ (‖Ψ z‖ / Metric.infDist z Γ ^ 2) * Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0) := by
    simpa only [mul_zero] using hvalue.mul hinfDist
  refine Tendsto.congr' ?_ hproduct
  filter_upwards with z
  by_cases hz : Metric.infDist z Γ = 0
  · simp only [hz, pow_two, mul_zero, div_zero]
  · field_simp

end Filter

namespace Set

variable {E : Type u} {F : Type v} [Zero F]

/-- The extension by zero from the complement of a set vanishes on that set. -/
theorem indicator_compl_eqOn_zero (Γ : Set E) (Ψ : E → F) :
    EqOn (Γᶜ.indicator Ψ) 0 Γ := by
  intro x hx
  have hxcompl : x ∉ Γᶜ := by
    simpa only [mem_compl_iff, not_not] using hx
  rw [indicator_of_notMem hxcompl]
  rfl

end Set

namespace IsClosed

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The first derivative of a zero extension vanishes identically on the closed set when
the source function has the required first-order distance decay. -/
theorem fderiv_indicator_compl_eqOn_zero
    (Γ : Set E) (Ψ : E → F) (hΓ : IsClosed Γ)
    (hΨ : DifferentiableOn ℝ Ψ Γᶜ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0)) :
    EqOn (fderiv ℝ (Γᶜ.indicator Ψ)) 0 Γ := by
  intro x hx
  exact fderiv_indicator_compl_eq_zero_of_mem Γ Ψ hΓ hΨ hvalue hx

/-- Quadratic value decay is sufficient for the first derivative of a zero extension to
vanish identically on the closed set. -/
theorem fderiv_indicator_compl_eqOn_zero_of_quadratic_value_decay
    (Γ : Set E) (Ψ : E → F) (hΓ : IsClosed Γ)
    (hΨ : DifferentiableOn ℝ Ψ Γᶜ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0)) :
    EqOn (fderiv ℝ (Γᶜ.indicator Ψ)) 0 Γ := by
  apply fderiv_indicator_compl_eqOn_zero Γ Ψ hΓ hΨ
  exact Filter.tendsto_norm_div_infDist_of_sq Γ Ψ hvalue

/-- The gradient of a scalar-valued zero extension vanishes identically on the closed set
when the source function has the required first-order distance decay. -/
theorem gradient_indicator_compl_eqOn_zero
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Γ : Set E) (Ψ : E → ℝ) (hΓ : IsClosed Γ)
    (hΨ : DifferentiableOn ℝ Ψ Γᶜ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0)) :
    EqOn (gradient (Γᶜ.indicator Ψ)) 0 Γ := by
  intro x hx
  exact gradient_indicator_compl_eq_zero_of_mem Γ Ψ hΓ hΨ hvalue hx

/-- Quadratic value decay is sufficient for the gradient of a scalar-valued zero extension
to vanish identically on the closed set. -/
theorem gradient_indicator_compl_eqOn_zero_of_quadratic_value_decay
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Γ : Set E) (Ψ : E → ℝ) (hΓ : IsClosed Γ)
    (hΨ : DifferentiableOn ℝ Ψ Γᶜ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0)) :
    EqOn (gradient (Γᶜ.indicator Ψ)) 0 Γ := by
  apply gradient_indicator_compl_eqOn_zero Γ Ψ hΓ hΨ
  exact Filter.tendsto_norm_div_infDist_of_sq Γ Ψ hvalue

/-- The second Fréchet derivative of a zero extension vanishes identically on the closed
set when the source value and first derivative have the required second-order decay. -/
theorem fderiv_fderiv_indicator_compl_eqOn_zero
    (Γ : Set E) (Ψ : E → F) (hΓ : IsClosed Γ)
    (hΨ : ContDiffOn ℝ 2 Ψ Γᶜ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0))
    (hderiv : Tendsto (fun z ↦ ‖fderiv ℝ Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0)) :
    EqOn (fderiv ℝ (fderiv ℝ (Γᶜ.indicator Ψ))) 0 Γ := by
  intro x hx
  exact fderiv_fderiv_indicator_compl_eq_zero_of_mem Γ Ψ hΓ hΨ hvalue hderiv hx

end IsClosed

namespace EuclideanPlane

variable (Γ : Set (EuclideanSpace ℝ (Fin 2)))
variable (Ψ : EuclideanSpace ℝ (Fin 2) → ℝ)

/-- The operator-valued Hessian of a planar zero extension vanishes identically on the
closed set under the second-order value and first-derivative decay assumptions. -/
theorem hessian_indicator_compl_eqOn_zero
    (hΓ : IsClosed Γ)
    (hΨ : ContDiffOn ℝ 2 Ψ Γᶜ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0))
    (hderiv : Tendsto (fun z ↦ ‖fderiv ℝ Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0)) :
    EqOn (hessian (Γᶜ.indicator Ψ)) 0 Γ := by
  intro x hx
  exact hessian_indicator_compl_eq_zero_of_mem Γ Ψ hΓ hΨ hvalue hderiv hx

end EuclideanPlane
