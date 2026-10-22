/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_28_Second_order_zero_jet_extension_across_a_closed_accumulation.lean
-/

module

import ReasLib.Analysis.Calculus.ContDiff.ZeroExtension

open Filter Set Topology

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/- Infrastructure I.28 (Second-order zero-jet extension across a closed accumulation set):
a `C²` function off a closed set extends by zero to a global `C²` function when its value,
first derivative, and second derivative satisfy the stated distance-decay limits. -/
#check (IsClosed.contDiff_two_indicator_compl :
  ∀ (Γ : Set E) (Ψ : E → F), IsClosed Γ → ContDiffOn ℝ 2 Ψ Γᶜ →
    Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0) →
    Tendsto (fun z ↦ ‖fderiv ℝ Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0) →
    Tendsto (fun z ↦ ‖fderiv ℝ (fderiv ℝ Ψ) z‖)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0) →
    ContDiff ℝ 2 (Γᶜ.indicator Ψ))
