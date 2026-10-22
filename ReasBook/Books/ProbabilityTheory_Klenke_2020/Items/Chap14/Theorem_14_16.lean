/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Definition_4_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal

universe u v

variable {Ω₁ : Type u} {Ω₂ : Type v} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂)

/- Source-facing layer: Theorem 14.16 is the chapter's product-measure Tonelli-Fubini theorem for
`EReal`-valued functions. The core/canonical owner abstraction is mathlib's product-measure
`lintegral` API: `Measurable.lintegral_prod_right'`, `Measurable.lintegral_prod_left'`,
`lintegral_prod`, and `lintegral_prod_symm'`. The chapter-level `erealIntegral` is the bridge/view
used in the `ℒ¹` branch: the measurable representative is the iterated difference of lower
integrals, and it agrees a.e. with the actual sectionwise `erealIntegral`. -/

private theorem measurable_ereal_abs_map : Measurable (fun x : EReal ↦ EReal.abs x) := by
  refine EReal.measurable_of_measurable_real ?_
  simpa [EReal.abs_def] using ENNReal.measurable_ofReal.comp continuous_abs.measurable

section

variable {f : Ω₁ × Ω₂ → EReal}

/-- Theorem 14.16: the right iterated lower integral in Tonelli's theorem is measurable. -/
theorem measurable_tonelli_right [SFinite μ₂] (hf : Measurable f) :
    Measurable (fun ω₁ ↦ ∫⁻ ω₂, (f (ω₁, ω₂)).toENNReal ∂μ₂) := by
  simpa using hf.ereal_toENNReal.lintegral_prod_right'

/-- Theorem 14.16: the left iterated lower integral in Tonelli's theorem is measurable. -/
theorem measurable_tonelli_left [SFinite μ₁] (hf : Measurable f) :
    Measurable (fun ω₂ ↦ ∫⁻ ω₁, (f (ω₁, ω₂)).toENNReal ∂μ₁) := by
  simpa using hf.ereal_toENNReal.lintegral_prod_left'

/-- The `ℒ¹` branch of Theorem 14.16: for almost every `ω₁`, the right section
`ω₂ ↦ f (ω₁, ω₂)` is textbook `μ₂`-integrable. -/
theorem erealIntegrable_prod_right_ae [SFinite μ₂] (hf : erealIntegrable f (μ₁.prod μ₂)) :
    ∀ᵐ ω₁ ∂μ₁, erealIntegrable (fun ω₂ ↦ f (ω₁, ω₂)) μ₂ := by
  have h_abs_meas : Measurable (fun z ↦ (f z).abs) :=
    measurable_ereal_abs_map.comp hf.1
  have h_section_meas : Measurable (fun ω₁ ↦ ∫⁻ ω₂, (f (ω₁, ω₂)).abs ∂μ₂) := by
    simpa using h_abs_meas.lintegral_prod_right'
  have h_outer_ne_top : ∫⁻ ω₁, ∫⁻ ω₂, (f (ω₁, ω₂)).abs ∂μ₂ ∂μ₁ ≠ ∞ := by
    rw [← lintegral_prod (fun z ↦ (f z).abs) h_abs_meas.aemeasurable]
    exact ne_of_lt <| by simpa [hasFiniteIntegral_def] using hf.2
  filter_upwards [ae_lt_top h_section_meas h_outer_ne_top] with ω₁ hω₁
  refine ⟨hf.1.comp measurable_prodMk_left, ?_⟩
  rw [hasFiniteIntegral_def]
  simpa using hω₁

/-- The `ℒ¹` branch of Theorem 14.16: for almost every `ω₂`, the left section
`ω₁ ↦ f (ω₁, ω₂)` is textbook `μ₁`-integrable. -/
theorem erealIntegrable_prod_left_ae [SFinite μ₁] [SFinite μ₂]
    (hf : erealIntegrable f (μ₁.prod μ₂)) :
    ∀ᵐ ω₂ ∂μ₂, erealIntegrable (fun ω₁ ↦ f (ω₁, ω₂)) μ₁ := by
  have h_abs_meas : Measurable (fun z ↦ (f z).abs) :=
    measurable_ereal_abs_map.comp hf.1
  have h_section_meas : Measurable (fun ω₂ ↦ ∫⁻ ω₁, (f (ω₁, ω₂)).abs ∂μ₁) := by
    simpa using h_abs_meas.lintegral_prod_left'
  have h_outer_ne_top : ∫⁻ ω₂, ∫⁻ ω₁, (f (ω₁, ω₂)).abs ∂μ₁ ∂μ₂ ≠ ∞ := by
    rw [← lintegral_prod_symm' (fun z : Ω₁ × Ω₂ ↦ (f z).abs) h_abs_meas]
    exact ne_of_lt <| by simpa [hasFiniteIntegral_def] using hf.2
  filter_upwards [ae_lt_top h_section_meas h_outer_ne_top] with ω₂ hω₂
  refine ⟨hf.1.comp measurable_prodMk_right, ?_⟩
  rw [hasFiniteIntegral_def]
  simpa using hω₂

/-- Theorem 14.16: the canonical `toENNReal` form of the nonnegative Tonelli identity, in
right-iterated order. For `f ≥ 0`, this is exactly the textbook branch. -/
theorem tonelli_right [SFinite μ₂] (hf : Measurable f) :
    ∫⁻ z, (f z).toENNReal ∂μ₁.prod μ₂ =
      ∫⁻ ω₁, ∫⁻ ω₂, (f (ω₁, ω₂)).toENNReal ∂μ₂ ∂μ₁ := by
  simpa using lintegral_prod (fun z ↦ (f z).toENNReal) hf.ereal_toENNReal.aemeasurable

/-- Theorem 14.16: the canonical `toENNReal` form of the nonnegative Tonelli identity, in
left-iterated order. For `f ≥ 0`, this is exactly the symmetric textbook branch. -/
theorem tonelli_left [SFinite μ₁] [SFinite μ₂] (hf : Measurable f) :
    ∫⁻ z, (f z).toENNReal ∂μ₁.prod μ₂ =
      ∫⁻ ω₂, ∫⁻ ω₁, (f (ω₁, ω₂)).toENNReal ∂μ₁ ∂μ₂ := by
  simpa using lintegral_prod_symm' (fun z : Ω₁ × Ω₂ ↦ (f z).toENNReal) hf.ereal_toENNReal

/-- The `ℒ¹` branch of Theorem 14.16: the right-iterated extended-real section integral has a
canonical measurable representative. -/
theorem measurable_erealIntegral_right [SFinite μ₂] (hf : erealIntegrable f (μ₁.prod μ₂)) :
    Measurable (fun ω₁ ↦
      (((∫⁻ ω₂, (f (ω₁, ω₂)).toENNReal ∂μ₂) : EReal) -
        ((∫⁻ ω₂, (-f (ω₁, ω₂)).toENNReal ∂μ₂) : EReal))) := by
  have h_pos : Measurable (fun ω₁ ↦ ∫⁻ ω₂, (f (ω₁, ω₂)).toENNReal ∂μ₂) := by
    simpa using hf.1.ereal_toENNReal.lintegral_prod_right'
  have h_neg : Measurable (fun ω₁ ↦ ∫⁻ ω₂, (-f (ω₁, ω₂)).toENNReal ∂μ₂) := by
    simpa using hf.1.neg.ereal_toENNReal.lintegral_prod_right'
  exact h_pos.coe_ereal_ennreal.sub h_neg.coe_ereal_ennreal

/-- The `ℒ¹` branch of Theorem 14.16: the left-iterated extended-real section integral has a
canonical measurable representative. -/
theorem measurable_erealIntegral_left [SFinite μ₁] (hf : erealIntegrable f (μ₁.prod μ₂)) :
    Measurable (fun ω₂ ↦
      (((∫⁻ ω₁, (f (ω₁, ω₂)).toENNReal ∂μ₁) : EReal) -
        ((∫⁻ ω₁, (-f (ω₁, ω₂)).toENNReal ∂μ₁) : EReal))) := by
  have h_pos : Measurable (fun ω₂ ↦ ∫⁻ ω₁, (f (ω₁, ω₂)).toENNReal ∂μ₁) := by
    simpa using hf.1.ereal_toENNReal.lintegral_prod_left'
  have h_neg : Measurable (fun ω₂ ↦ ∫⁻ ω₁, (-f (ω₁, ω₂)).toENNReal ∂μ₁) := by
    simpa using hf.1.neg.ereal_toENNReal.lintegral_prod_left'
  exact h_pos.coe_ereal_ennreal.sub h_neg.coe_ereal_ennreal

/-- The measurable representative in the right-iterated `ℒ¹` branch agrees a.e. with the actual
sectionwise textbook `EReal` integral. -/
theorem ae_eq_erealIntegral_right [SFinite μ₂] (hf : erealIntegrable f (μ₁.prod μ₂)) :
    ∀ᵐ ω₁ ∂μ₁,
      ∃ hω₁ : erealIntegrable (fun ω₂ ↦ f (ω₁, ω₂)) μ₂,
        (((∫⁻ ω₂, (f (ω₁, ω₂)).toENNReal ∂μ₂) : EReal) -
          ((∫⁻ ω₂, (-f (ω₁, ω₂)).toENNReal ∂μ₂) : EReal)) =
            erealIntegral (fun ω₂ ↦ f (ω₁, ω₂)) μ₂ hω₁.defined := by
  filter_upwards [erealIntegrable_prod_right_ae μ₁ μ₂ hf] with ω₁ hω₁
  exact ⟨hω₁, by rw [erealIntegral_spec]⟩

/-- The measurable representative in the left-iterated `ℒ¹` branch agrees a.e. with the actual
sectionwise textbook `EReal` integral. -/
theorem ae_eq_erealIntegral_left [SFinite μ₁] [SFinite μ₂]
    (hf : erealIntegrable f (μ₁.prod μ₂)) :
    ∀ᵐ ω₂ ∂μ₂,
      ∃ hω₂ : erealIntegrable (fun ω₁ ↦ f (ω₁, ω₂)) μ₁,
        (((∫⁻ ω₁, (f (ω₁, ω₂)).toENNReal ∂μ₁) : EReal) -
          ((∫⁻ ω₁, (-f (ω₁, ω₂)).toENNReal ∂μ₁) : EReal)) =
            erealIntegral (fun ω₁ ↦ f (ω₁, ω₂)) μ₁ hω₂.defined := by
  filter_upwards [erealIntegrable_prod_left_ae μ₁ μ₂ hf] with ω₂ hω₂
  exact ⟨hω₂, by rw [erealIntegral_spec]⟩

/-- Theorem 14.16: in right-iterated form, the chapter `EReal` integral over a product measure is
the difference of the iterated lower integrals of the positive and negative parts; by
`ae_eq_erealIntegral_right`, this measurable representative agrees a.e. with the actual
sectionwise textbook `EReal` integral. -/
theorem fubini_right [SFinite μ₂] (hf : erealIntegrable f (μ₁.prod μ₂)) :
    erealIntegral f (μ₁.prod μ₂) hf.defined =
      (((∫⁻ ω₁, ∫⁻ ω₂, (f (ω₁, ω₂)).toENNReal ∂μ₂ ∂μ₁) : EReal) -
        ((∫⁻ ω₁, ∫⁻ ω₂, (-f (ω₁, ω₂)).toENNReal ∂μ₂ ∂μ₁) : EReal)) := by
  rw [erealIntegral_spec]
  rw [tonelli_right μ₁ μ₂ hf.1, tonelli_right μ₁ μ₂ hf.1.neg]

/-- The symmetric Fubini identity for Theorem 14.16, with the order of the iterated lower
integrals reversed; by `ae_eq_erealIntegral_left`, this measurable representative agrees a.e. with
the actual sectionwise textbook `EReal` integral. -/
theorem fubini_left [SFinite μ₁] [SFinite μ₂] (hf : erealIntegrable f (μ₁.prod μ₂)) :
    erealIntegral f (μ₁.prod μ₂) hf.defined =
      (((∫⁻ ω₂, ∫⁻ ω₁, (f (ω₁, ω₂)).toENNReal ∂μ₁ ∂μ₂) : EReal) -
        ((∫⁻ ω₂, ∫⁻ ω₁, (-f (ω₁, ω₂)).toENNReal ∂μ₁ ∂μ₂) : EReal)) := by
  rw [erealIntegral_spec]
  rw [tonelli_left μ₁ μ₂ hf.1, tonelli_left μ₁ μ₂ hf.1.neg]

end
