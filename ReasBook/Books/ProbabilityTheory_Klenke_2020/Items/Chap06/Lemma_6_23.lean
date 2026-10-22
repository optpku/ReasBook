/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Use the stronger canonical mathlib theorem
-- `exists_pos_lintegral_lt_of_sigmaFinite`, which provides a measurable everywhere positive
-- `ℝ≥0`-valued function with finite integral, and then coerce it to an integrable real-valued map.
/-- Lemma 6.23: On a `σ`-finite measure space, there exists a real-valued integrable map that is
strictly positive `μ`-almost everywhere. -/
theorem exists_integrable_ae_strictly_pos (μ : Measure Ω) [SigmaFinite μ] :
    ∃ h : Ω → ℝ, Integrable h μ ∧ ∀ᵐ ω ∂μ, 0 < h ω := by
  obtain ⟨g, hg_pos, hg_meas, hg_int_lt⟩ :=
    exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  have hg_int_ne_top : ∫⁻ ω, g ω ∂μ ≠ ⊤ :=
    ne_of_lt <| hg_int_lt.trans_le le_top
  refine ⟨fun ω ↦ (g ω : ℝ), ?_, ?_⟩
  · simpa using
      integrable_toReal_of_lintegral_ne_top hg_meas.coe_nnreal_ennreal.aemeasurable hg_int_ne_top
  · exact ae_of_all μ fun ω ↦ by
      exact_mod_cast hg_pos ω
