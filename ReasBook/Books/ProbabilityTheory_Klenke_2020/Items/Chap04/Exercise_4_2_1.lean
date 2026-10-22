/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

-- Proof sketch: consider the superlevel sets `A_t = {ω | t ≤ |f ω|}`. For `t > 0`,
-- `Integrable.measure_norm_ge_lt_top` gives `μ A_t < ∞`. Choose `t` so that the tail `L¹`-mass of
-- `|f|` on `A_tᶜ = {ω | |f ω| < t}` is less than `ε`, then control the complementary set integral
-- using `norm_integral_le_integral_norm` and rewrite the difference with `integral_add_compl`.
/-- Exercise 4.2.1: every integrable real-valued function admits a measurable set of finite
measure whose complementary `L¹`-mass is less than `ε`. -/
theorem exists_set_finite_measure_integral_abs_compl_lt_of_integrable
    {f : Ω → ℝ} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A < ⊤ ∧
      ∫ x in Aᶜ, |f x| ∂μ < ε := by
  -- Convert the `L¹` assumption into finiteness of the `lintegral` of `|f|`.
  let I : ENNReal := ∫⁻ x, ‖f x‖ₑ ∂μ
  have hlin' : ∫⁻ x, ‖f x‖ₑ ∂μ < ⊤ := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (μ := μ) (f := f) hf]
    exact ENNReal.ofReal_lt_top
  have hlin : I < ⊤ := by
    simpa [I] using hlin'
  -- Apply the standard finite-measure truncation theorem to the nonnegative function `|f|`.
  obtain ⟨A, hA, hμA, htail⟩ :=
    exists_setLIntegral_compl_lt (μ := μ) (f := fun x ↦ ‖f x‖ₑ)
      (lt_top_iff_ne_top.mp <| by simpa [I] using hlin)
      (ENNReal.ofReal_ne_zero_iff.mpr hε)
  refine ⟨A, hA, hμA, ?_⟩
  -- Reinterpret the tail `lintegral` on `Aᶜ` as the real set integral of `|f|`.
  have hAint : Integrable f (μ.restrict Aᶜ) := by
    simpa [IntegrableOn] using (hf.integrableOn (s := Aᶜ))
  have htail' : ENNReal.ofReal (∫ x in Aᶜ, ‖f x‖ ∂μ) < ENNReal.ofReal ε := by
    rw [ofReal_integral_norm_eq_lintegral_enorm (μ := μ.restrict Aᶜ) (f := f) hAint]
    simpa using htail
  -- The `ENNReal` inequality descends to the desired real inequality.
  simpa [Real.norm_eq_abs] using (ENNReal.ofReal_lt_ofReal_iff hε).mp htail'

/-- Textbook reformulation of Exercise 4.2.1. -/
theorem exists_set_finite_measure_integral_sub_lt_of_integrable
    {f : Ω → ℝ} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A < ⊤ ∧
      |(∫ x in A, f x ∂μ) - ∫ x, f x ∂μ| < ε := by
  obtain ⟨A, hA, hμA, htail⟩ := exists_set_finite_measure_integral_abs_compl_lt_of_integrable hf hε
  refine ⟨A, hA, hμA, ?_⟩
  have hsub : (∫ x in A, f x ∂μ) - ∫ x, f x ∂μ = -(∫ x in Aᶜ, f x ∂μ) := by
    have hadd := integral_add_compl hA hf
    linarith
  have hnorm : |∫ x in Aᶜ, f x ∂μ| ≤ ∫ x in Aᶜ, |f x| ∂μ := by
    rw [← Real.norm_eq_abs]
    let ν : Measure Ω := μ.restrict Aᶜ
    change ‖∫ x, f x ∂ν‖ ≤ ∫ x, ‖f x‖ ∂ν
    simpa [ν] using norm_integral_le_integral_norm (fun x ↦ f x)
  calc
    |(∫ x in A, f x ∂μ) - ∫ x, f x ∂μ|
        = |∫ x in Aᶜ, f x ∂μ| := by rw [hsub, abs_neg]
    _ ≤ ∫ x in Aᶜ, |f x| ∂μ := hnorm
    _ < ε := htail
