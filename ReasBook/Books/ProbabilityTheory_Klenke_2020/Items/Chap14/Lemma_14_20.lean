/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Definition_8_25

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

section FiniteTransitionKernel

variable {Ω₁ : Type u} {Ω₂ : Type v} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

open ProbabilityTheory.Kernel

private theorem measurable_lintegral_indicator_const_of_finite
    (κ : Kernel Ω₁ Ω₂) (hκ : ∀ ω₁, IsFiniteMeasure (κ ω₁)) {t : Set (Ω₁ × Ω₂)}
    (ht : MeasurableSet t) (c : ℝ≥0∞) :
    Measurable (fun ω₁ ↦ ∫⁻ ω₂, t.indicator (fun _ ↦ c) (ω₁, ω₂) ∂κ ω₁) := by
  simp_rw [lintegral_indicator_const_comp measurable_prodMk_left ht]
  exact Measurable.const_mul (measurable_kernel_prodMk_left_of_finite ht hκ) c

-- Proof sketch: first use the preceding product-section measurability lemma to see that each
-- section `ω₂ ↦ f (ω₁, ω₂)` is measurable, so the fiberwise `lintegral` is well defined. Then
-- prove measurability first for indicator functions of measurable rectangles, extend to all
-- measurable sets by a π-λ argument, then to simple functions by linearity, and finally pass to
-- general nonnegative measurable functions by monotone convergence.
/-- Lemma 14.20: for a finite transition kernel `κ` and a nonnegative measurable function
`f : Ω₁ × Ω₂ → ℝ≥0∞`, the fiberwise integral `ω₁ ↦ ∫⁻ ω₂, f (ω₁, ω₂) ∂κ ω₁` is a measurable
map on `Ω₁`. This is the textbook map `I_f`; its well-definedness is encoded by the use of the
nonnegative Lebesgue integral. -/
theorem measurable_lintegral_finite_transition_kernel
    (κ : Kernel Ω₁ Ω₂) (hκ : IsFiniteTransitionKernel κ) {f : Ω₁ × Ω₂ → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fun ω₁ ↦ ∫⁻ ω₂, f (ω₁, ω₂) ∂κ ω₁) := by
  let F : ℕ → SimpleFunc (Ω₁ × Ω₂) ℝ≥0∞ := SimpleFunc.eapprox f
  have hF : ∀ x, ⨆ n, F n x = f x := SimpleFunc.iSup_eapprox_apply hf
  simp_rw [← hF]
  have h_iSup :
      ∀ ω₁, (∫⁻ ω₂, ⨆ n, F n (ω₁, ω₂) ∂κ ω₁) = ⨆ n, ∫⁻ ω₂, F n (ω₁, ω₂) ∂κ ω₁ := by
    intro ω₁
    rw [lintegral_iSup]
    · intro n
      exact (F n).measurable.comp measurable_prodMk_left
    · intro i j hij ω₂
      exact SimpleFunc.monotone_eapprox f hij (ω₁, ω₂)
  simp_rw [h_iSup]
  refine Measurable.iSup ?_
  intro n
  refine SimpleFunc.induction ?_ ?_ (F n)
  · intro c t ht
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    exact measurable_lintegral_indicator_const_of_finite κ hκ ht c
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have h_add :
        (fun ω₁ ↦ ∫⁻ ω₂, g₁ (ω₁, ω₂) + g₂ (ω₁, ω₂) ∂κ ω₁) =
          (fun ω₁ ↦ ∫⁻ ω₂, g₁ (ω₁, ω₂) ∂κ ω₁) +
            fun ω₁ ↦ ∫⁻ ω₂, g₂ (ω₁, ω₂) ∂κ ω₁ := by
      ext ω₁
      rw [Pi.add_apply, lintegral_add_left]
      exact (by fun_prop)
    rw [h_add]
    exact Measurable.add hm₁ hm₂

end FiniteTransitionKernel
