/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory
open scoped ENNReal

variable {Ω : Type u} [MeasurableSpace Ω]

private theorem toENNReal_le_abs (x : EReal) : x.toENNReal ≤ x.abs := by
  cases x with
  | bot => simp [EReal.toENNReal]
  | top => simp [EReal.toENNReal]
  | coe a =>
      simp [EReal.abs_def, EReal.toENNReal, le_abs_self]

/-- Definition 4.7: A measurable `EReal`-valued function is `μ`-integrable when its absolute
value has finite lower integral. In Lean, this finiteness condition is the canonical predicate
`HasFiniteIntegral` applied to the `ENNReal`-valued function `EReal.abs ∘ f`. -/
def erealIntegrable (f : Ω → EReal) (μ : Measure Ω) : Prop :=
  Measurable f ∧ HasFiniteIntegral (fun ω ↦ (f ω).abs) μ

/-- The textbook domain on which the extended-real integral is defined by the difference of the
lower integrals of the positive and negative parts: `f` is measurable and at least one of the two
parts has finite lower integral. -/
def erealIntegralDefined (f : Ω → EReal) (μ : Measure Ω) : Prop :=
  Measurable f ∧
    (HasFiniteIntegral (fun ω ↦ (f ω).toENNReal) μ ∨
      HasFiniteIntegral (fun ω ↦ (-f ω).toENNReal) μ)

/-- For a textbook `μ`-integrable extended-real-valued function, the positive part has finite
lower integral. -/
theorem erealIntegrable.hasFiniteIntegral_toENNReal {f : Ω → EReal} {μ : Measure Ω}
    (hf : erealIntegrable f μ) :
    HasFiniteIntegral (fun ω ↦ (f ω).toENNReal) μ := by
  rcases hf with ⟨_, hf_abs⟩
  rw [hasFiniteIntegral_def] at hf_abs ⊢
  exact lt_of_le_of_lt (lintegral_mono fun ω ↦ toENNReal_le_abs (f ω)) hf_abs

/-- For a textbook `μ`-integrable extended-real-valued function, the negative part has finite
lower integral. -/
theorem erealIntegrable.hasFiniteIntegral_neg_toENNReal {f : Ω → EReal} {μ : Measure Ω}
    (hf : erealIntegrable f μ) :
    HasFiniteIntegral (fun ω ↦ (-f ω).toENNReal) μ := by
  rcases hf with ⟨_, hf_abs⟩
  have hf_neg_abs : (∫⁻ ω, (-f ω).abs ∂μ) < ∞ := by
    simpa [EReal.abs_neg] using hf_abs
  rw [hasFiniteIntegral_def]
  simpa [EReal.abs_neg] using
    (lt_of_le_of_lt (lintegral_mono fun ω ↦ toENNReal_le_abs (-f ω)) hf_neg_abs)

/-- Every textbook `μ`-integrable extended-real-valued function has a well-defined extended-real
integral. -/
theorem erealIntegrable.defined {f : Ω → EReal} {μ : Measure Ω} (hf : erealIntegrable f μ) :
    erealIntegralDefined f μ := by
  exact ⟨hf.1, Or.inl hf.hasFiniteIntegral_toENNReal⟩

/-- An integrable lower bound gives a well-defined textbook extended-real integral. -/
theorem erealIntegralDefined_of_ae_le {f g : Ω → EReal} {μ : Measure Ω}
    (hg : erealIntegrable g μ) (hf_meas : Measurable f) (hgf : g ≤ᵐ[μ] f) :
    erealIntegralDefined f μ := by
  refine ⟨hf_meas, Or.inr ?_⟩
  have hg_neg := hg.hasFiniteIntegral_neg_toENNReal
  rw [hasFiniteIntegral_def] at hg_neg ⊢
  have hneg_mono : ∀ᵐ ω ∂μ, (-f ω).toENNReal ≤ (-g ω).toENNReal :=
    hgf.mono fun ω hω ↦ EReal.toENNReal_le_toENNReal <| by
      simpa using EReal.neg_le_neg_iff.2 hω
  exact lt_of_le_of_lt (lintegral_mono_ae hneg_mono) hg_neg

/-- The textbook extended-real integral is the difference of the lower integrals of the positive
and negative parts, and is only defined on `erealIntegralDefined f μ`. -/
noncomputable def erealIntegral (f : Ω → EReal) (μ : Measure Ω)
    (_ : erealIntegralDefined f μ) : EReal :=
  ((∫⁻ ω, (f ω).toENNReal ∂μ) : EReal) - ((∫⁻ ω, (-f ω).toENNReal ∂μ) : EReal)

/-- Definition 4.7 companion: on its domain of definition, the textbook extended-real integral is
represented in Lean by the difference of the lower integrals of the positive and negative parts. -/
@[simp] theorem erealIntegral_spec {f : Ω → EReal} {μ : Measure Ω}
    (hf : erealIntegralDefined f μ) :
    erealIntegral f μ hf =
      ((∫⁻ ω, (f ω).toENNReal ∂μ) : EReal) - ((∫⁻ ω, (-f ω).toENNReal ∂μ) : EReal) :=
  rfl
