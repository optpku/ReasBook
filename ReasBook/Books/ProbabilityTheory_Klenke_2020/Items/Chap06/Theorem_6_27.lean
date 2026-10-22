/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {X : Type v} [TopologicalSpace X] [FirstCountableTopology X]

-- Proof sketch: apply `continuousAt_of_dominated` to the parameter-first family `x ↦ f x`,
-- using integrability of each section to obtain a.e.-strong measurability and the common
-- integrable majorant `bound` for domination.
/-- Theorem 6.27: if each section `ω ↦ f x ω` is integrable, `x ↦ f x ω` is continuous at `x₀`
for almost every `ω`, and all sections are almost everywhere dominated by a single integrable
function `bound`, then the parameter integral `x ↦ ∫ ω, f x ω ∂μ` is continuous at `x₀`. -/
theorem continuousAt_integral_of_dominated_of_ae_continuousAt
    {f : X → Ω → ℝ} {x₀ : X} {bound : Ω → ℝ}
    (hf_integrable : ∀ x : X, Integrable (f x) μ)
    (hf_continuousAt : ∀ᵐ ω ∂μ, ContinuousAt (fun x ↦ f x ω) x₀)
    (h_bound_integrable : Integrable bound μ)
    (h_dom : ∀ x : X, ∀ᵐ ω ∂μ, |f x ω| ≤ bound ω) :
    ContinuousAt (fun x ↦ ∫ ω, f x ω ∂μ) x₀ := by
  refine continuousAt_of_dominated
    (Eventually.of_forall fun x ↦ (hf_integrable x).aestronglyMeasurable)
    ?_ h_bound_integrable hf_continuousAt
  refine Eventually.of_forall fun x ↦ ?_
  filter_upwards [h_dom x] with ω hω
  simpa [Real.norm_eq_abs] using hω
