/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: use a σ-finite exhaustion `spanningSets ν n`; on each finite-measure piece,
-- restrict both density identities and apply the canonical finite-total-mass uniqueness theorem
-- `withDensity_eq_iff`, then assemble the resulting restricted almost-everywhere equalities.
/-- Theorem 7.29: if `ν` is σ-finite and `f₁`, `f₂` are measurable densities of `ν` with
respect to `μ`, then `f₁` and `f₂` agree `μ`-almost everywhere. In particular, the density
`dν/dμ` is unique up to `μ`-almost everywhere equality. -/
theorem densities_ae_eq_of_withDensity_eq {μ ν : Measure Ω} [SigmaFinite ν]
    {f₁ f₂ : Ω → ℝ≥0∞} (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    (h₁ : μ.withDensity f₁ = ν) (h₂ : μ.withDensity f₂ = ν) :
    f₁ =ᵐ[μ] f₂ := by
  have h_spanning :
      ∀ n, ∀ᵐ x ∂μ, x ∈ spanningSets ν n → f₁ x = f₂ x := by
    intro n
    let s := spanningSets ν n
    have hs : MeasurableSet s := measurableSet_spanningSets ν n
    have hνs : ν s < ∞ := measure_spanningSets_lt_top ν n
    have h_restrict :
        (μ.restrict s).withDensity f₁ = (μ.restrict s).withDensity f₂ := by
      rw [← restrict_withDensity hs, h₁, ← h₂, restrict_withDensity hs]
    have hf₁_lt_top : ∫⁻ x, f₁ x ∂μ.restrict s ≠ ∞ := by
      rw [← withDensity_apply _ hs, h₁]
      exact hνs.ne
    exact (ae_restrict_iff' hs).mp <|
      (withDensity_eq_iff hf₁.aemeasurable.restrict hf₂.aemeasurable.restrict hf₁_lt_top).mp
        h_restrict
  filter_upwards [ae_all_iff.2 h_spanning] with x hx
  exact hx (spanningSetsIndex ν x) (mem_spanningSetsIndex ν x)

/-
The canonical owner identity for densities against a `σ`-finite base measure is
`Measure.rnDeriv_withDensity`.
-/
recall MeasureTheory.Measure.rnDeriv_withDensity

-- Proof sketch: rewrite `ν` using `h_density` and apply the canonical identity
-- `Measure.rnDeriv_withDensity`.
/-- Any measurable density of `ν` with respect to a σ-finite measure `μ` agrees `μ`-almost
everywhere with the canonical Radon-Nikodym derivative `ν.rnDeriv μ`. -/
theorem density_ae_eq_rnDeriv_of_withDensity_eq {μ ν : Measure Ω} [SigmaFinite μ]
    {f : Ω → ℝ≥0∞} (hf : Measurable f) (h_density : μ.withDensity f = ν) :
    f =ᵐ[μ] ν.rnDeriv μ := by
  rw [← h_density]
  exact (Measure.rnDeriv_withDensity μ hf).symm
