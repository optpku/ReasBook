module

public import ReasLib.Analysis.Calculus.ContDiff.ZeroExtensionJets
public import ReasLib.Analysis.Calculus.EuclideanPlaneHessian

public section

open Filter Set Topology

namespace EuclideanPlane

open scoped Topology

variable (Γ : Set (EuclideanSpace ℝ (Fin 2)))
variable (Ψ : EuclideanSpace ℝ (Fin 2) → ℝ)

/-- A zero extension across a closed subset of the Euclidean plane has vanishing operator-valued
Hessian at every boundary point under the usual second-order value and first-derivative decay. -/
theorem hessian_indicator_compl_eq_zero_of_mem
    (hΓ : IsClosed Γ)
    (hΨ : ContDiffOn ℝ 2 Ψ Γᶜ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0))
    (hderiv : Tendsto (fun z ↦ ‖fderiv ℝ Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0))
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ Γ) :
    hessian (Γᶜ.indicator Ψ) x = 0 := by
  have hsecond := IsClosed.fderiv_fderiv_indicator_compl_eq_zero_of_mem
    Γ Ψ hΓ hΨ hvalue hderiv hx
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_left ℝ
  intro v
  rw [real_inner_comm ((hessian (Γᶜ.indicator Ψ) x) u) v, hessian_apply_inner,
    iteratedFDeriv_two_apply, hsecond]
  simp

end EuclideanPlane
