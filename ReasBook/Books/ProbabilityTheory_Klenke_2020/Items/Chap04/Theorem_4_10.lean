/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Definition_4_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal

universe u v

variable {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Helper for Theorem 4.10: absolute value on `EReal` is a measurable map. -/
private theorem measurable_ereal_abs_map : Measurable (fun x : EReal ↦ EReal.abs x) := by
  -- Reduce measurability on `EReal` to the corresponding real-valued absolute-value map.
  refine EReal.measurable_of_measurable_real ?_
  simpa [EReal.abs_def] using ENNReal.measurable_ofReal.comp continuous_abs.measurable

-- Proof sketch: compose measurability using `Measurable.comp`, then apply `lintegral_map` to the
-- absolute value `EReal.abs ∘ f` along the measurable map `X`.
/-- Helper for Theorem 4.10: if `f` is `erealIntegrable` against the pushforward measure `μ.map X`,
then `f ∘ X` is `erealIntegrable` against `μ`. -/
theorem erealIntegrable_comp_of_map {μ : Measure Ω} {X : Ω → Ω'}
    (hX : Measurable X) {f : Ω' → EReal}
    (hf : erealIntegrable f (μ.map X)) :
    erealIntegrable (f ∘ X) μ := by
  rcases hf with ⟨hf_meas, hf_integrable⟩
  -- Transport the absolute-value lower integral back across the pushforward measure.
  have habs : ∫⁻ ω, (f (X ω)).abs ∂μ = ∫⁻ x, (f x).abs ∂μ.map X := by
    simpa [Function.comp_apply] using
      (lintegral_map (measurable_ereal_abs_map.comp hf_meas) hX).symm
  -- The composed function is measurable, and its absolute-value integral is finite by `habs`.
  refine ⟨hf_meas.comp hX, ?_⟩
  rw [hasFiniteIntegral_def] at hf_integrable ⊢
  simpa [Function.comp_apply, habs] using hf_integrable

-- Proof sketch: apply `lintegral_map` to the positive part `EReal.toENNReal ∘ f` and the
-- negative part `EReal.toENNReal ∘ (-f)` along `X`, then rewrite the defining formula.
/-- Theorem 4.10: For a measurable map `X`, integrating `f` against the pushforward measure
`μ.map X` agrees with integrating `f ∘ X` against `μ`. -/
theorem erealIntegral_map {μ : Measure Ω} {X : Ω → Ω'}
    (hX : Measurable X) {f : Ω' → EReal}
    (hf : erealIntegrable f (μ.map X)) :
    erealIntegral f (μ.map X) hf.defined =
      erealIntegral (f ∘ X) μ (erealIntegrable_comp_of_map hX hf).defined := by
  -- Transport the positive and negative lower integrals separately through `μ.map X`.
  have hpos : ∫⁻ ω, (f (X ω)).toENNReal ∂μ = ∫⁻ x, (f x).toENNReal ∂μ.map X := by
    simpa [Function.comp_apply] using (lintegral_map hf.1.ereal_toENNReal hX).symm
  have hneg : ∫⁻ ω, (-f (X ω)).toENNReal ∂μ = ∫⁻ x, (-f x).toENNReal ∂μ.map X := by
    simpa [Function.comp_apply] using (lintegral_map hf.1.neg.ereal_toENNReal hX).symm
  -- Expand both integrals by definition and substitute the transported lower integrals.
  rw [erealIntegral_spec, erealIntegral_spec]
  simp_rw [Function.comp_apply]
  rw [hpos, hneg]
