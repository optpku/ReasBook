/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Definition_4_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Corollary_14_23

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u v

section

variable {Ω₁ : Type u} {Ω₂ : Type v}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/- Source-facing layer: Theorem 14.29 is about the canonical product measure from Corollary 14.23
attached to a finite measure `μ` and a finite transition kernel `κ`. The core/canonical
integration engine is the product-measure Tonelli/Fubini API from Theorem 14.16; a direct
`μ ⊗ₘ κ` formulation is only a stronger bridge/view when extra mathlib s-finiteness hypotheses are
available. -/
variable (μ : Measure Ω₁) [IsFiniteMeasure μ] (κ : Kernel Ω₁ Ω₂)

/-- Helper for Theorem 14.29: fix `ω₁` and push `κ ω₁` forward along `ω₂ ↦ (ω₁, ω₂)` to obtain a
measure on `Ω₁ × Ω₂`. -/
noncomputable def sectionPairMeasure (κ : Kernel Ω₁ Ω₂) (ω₁ : Ω₁) : Measure (Ω₁ × Ω₂) :=
  (κ ω₁).map (Prod.mk ω₁)

/-- Helper for Theorem 14.29: the family `ω₁ ↦ sectionPairMeasure κ ω₁` is measurable when `κ` is
rowwise finite. -/
lemma measurable_sectionPairMeasure
    (hκ : IsFiniteTransitionKernel κ) :
    Measurable (sectionPairMeasure κ) := by
  -- Proof comment: measurable-set evaluation reduces to the standard finite-kernel section-mass
  -- measurability lemma.
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [sectionPairMeasure, Measure.map_apply measurable_prodMk_left hs]
  exact Kernel.measurable_kernel_prodMk_left_of_finite (κ := κ) hs hκ

/-- Helper for Theorem 14.29: Corollary 14.23's canonical product measure agrees with the Chapter
14 product kernel from Theorem 14.22 specialized to `Kernel.const Unit μ` and
`Kernel.prodMkLeft Unit κ`. -/
lemma finiteTransitionKernelProductMeasure_eq_transitionKernelProduct
    (hκ : IsFiniteTransitionKernel κ) :
    finiteTransitionKernelProductMeasure μ κ hκ =
      transitionKernelProduct (Kernel.const Unit μ) (Kernel.prodMkLeft Unit κ) () := by
  let ν : Measure (Ω₁ × Ω₂) :=
    transitionKernelProduct (Kernel.const Unit μ) (Kernel.prodMkLeft Unit κ) ()
  have hconst : IsFiniteTransitionKernel (Kernel.const Unit μ) :=
    isFiniteTransitionKernel_of_isFiniteKernel (Kernel.const Unit μ)
  have hprodMkLeft : IsFiniteTransitionKernel (Kernel.prodMkLeft Unit κ) := by
    intro ω
    simpa [Kernel.prodMkLeft_apply] using hκ ω.2
  have hν :
      SigmaFinite ν ∧
        ∀ A₁ : Set Ω₁, ∀ A₂ : Set Ω₂,
          MeasurableSet A₁ → MeasurableSet A₂ →
            ν (A₁ ×ˢ A₂) = ∫⁻ ω₁ in A₁, κ ω₁ A₂ ∂μ := by
    refine ⟨?_, ?_⟩
    · -- Proof comment: Theorem 14.22 gives rowwise sigma-finiteness for the specialized product.
      exact transitionKernelProduct_isSigmaFiniteTransitionKernel
        (Kernel.const Unit μ) (Kernel.prodMkLeft Unit κ) hconst hprodMkLeft ()
    · intro A₁ A₂ hA₁ hA₂
      -- Proof comment: on rectangles, the specialized product kernel reduces to the textbook
      -- restricted integral formula.
      rw [transitionKernelProduct_prodMkLeft_apply
        (Kernel.const Unit μ) κ hconst hκ () (hA₁.prod hA₂)]
      rw [Kernel.const_apply]
      rw [← lintegral_indicator hA₁]
      refine lintegral_congr_ae <| Filter.Eventually.of_forall ?_
      intro ω₁
      by_cases hω₁ : ω₁ ∈ A₁
      · simp [hω₁]
      · simp [hω₁]
  let hex := existsUnique_sigmaFinite_product_measure_of_isFiniteTransitionKernel μ κ hκ
  -- Proof comment: Corollary 14.23 characterizes the canonical measure by the same sigma-finite
  -- rectangle formula, so uniqueness identifies it with `ν`.
  simpa [finiteTransitionKernelProductMeasure, ν] using ((Classical.choose_spec hex).2 ν hν).symm

/-- Helper for Theorem 14.29: the specialized product kernel from Theorem 14.22 is the bind of
the measurable family `ω₁ ↦ sectionPairMeasure κ ω₁`. -/
lemma transitionKernelProduct_eq_bind_sectionPairMeasure
    (hκ : IsFiniteTransitionKernel κ) :
    transitionKernelProduct (Kernel.const Unit μ) (Kernel.prodMkLeft Unit κ) () =
      μ.bind (sectionPairMeasure κ) := by
  have hconst : IsFiniteTransitionKernel (Kernel.const Unit μ) :=
    isFiniteTransitionKernel_of_isFiniteKernel (Kernel.const Unit μ)
  ext s hs
  -- Proof comment: both measures evaluate measurable sets by the same section integral.
  rw [transitionKernelProduct_prodMkLeft_apply (Kernel.const Unit μ) κ hconst hκ () hs,
    Measure.bind_apply hs (measurable_sectionPairMeasure (κ := κ) hκ).aemeasurable]
  simp only [sectionPairMeasure, Kernel.const_apply, Measure.map_apply measurable_prodMk_left hs]

/-- Helper for Theorem 14.29: the canonical product measure is the bind of the measurable family
`ω₁ ↦ sectionPairMeasure κ ω₁`. -/
lemma finiteTransitionKernelProductMeasure_eq_bind_sectionPairMeasure
    (hκ : IsFiniteTransitionKernel κ) :
    finiteTransitionKernelProductMeasure μ κ hκ = μ.bind (sectionPairMeasure κ) := by
  -- Proof comment: combine the uniqueness identification from Corollary 14.23 with the direct
  -- bind description of the specialized product kernel.
  rw [finiteTransitionKernelProductMeasure_eq_transitionKernelProduct (μ := μ) (κ := κ) hκ]
  exact transitionKernelProduct_eq_bind_sectionPairMeasure (μ := μ) (κ := κ) hκ

/-- Theorem 14.29: for the source-facing product measure determined by `μ` and `κ`, the canonical
right-iterated `toENNReal` Tonelli identity holds. -/
theorem tonelli_transition_kernel
    (hκ : IsFiniteTransitionKernel κ)
    {f : Ω₁ × Ω₂ → EReal} (hf : Measurable f) :
    ∫⁻ z, (f z).toENNReal ∂finiteTransitionKernelProductMeasure μ κ hκ =
      ∫⁻ ω₁, ∫⁻ ω₂, (f (ω₁, ω₂)).toENNReal ∂κ ω₁ ∂μ := by
  -- Proof comment: rewrite the source-facing measure as a bind of mapped section measures.
  rw [finiteTransitionKernelProductMeasure_eq_bind_sectionPairMeasure (μ := μ) (κ := κ) hκ]
  -- Proof comment: `lintegral_bind` moves the outer integral past the measurable family of
  -- section measures, and `lintegral_map` removes the pushforward along `Prod.mk ω₁`.
  rw [Measure.lintegral_bind (measurable_sectionPairMeasure (κ := κ) hκ).aemeasurable]
  · refine lintegral_congr_ae <| Filter.Eventually.of_forall ?_
    intro ω₁
    simpa [sectionPairMeasure, Function.comp_apply] using
      (lintegral_map (μ := κ ω₁)
        (f := fun z : Ω₁ × Ω₂ ↦ (f z).toENNReal)
        (g := Prod.mk ω₁) hf.ereal_toENNReal measurable_prodMk_left)
  · exact hf.ereal_toENNReal.aemeasurable

-- Proof sketch: after identifying `ν` with the Chapter 14 product measure from Corollary 14.23,
-- apply the right-iterated `EReal` Fubini theorem from Theorem 14.16.
/-- Theorem 14.29: for an `erealIntegrable` function on the product measure from Corollary 14.23,
the chapter `EReal` integral is the iterated difference of the positive-part and negative-part
lower integrals. -/
theorem fubini_transition_kernel
    (hκ : IsFiniteTransitionKernel κ)
    {f : Ω₁ × Ω₂ → EReal}
    (hf : erealIntegrable f (finiteTransitionKernelProductMeasure μ κ hκ)) :
    erealIntegral f (finiteTransitionKernelProductMeasure μ κ hκ) hf.defined =
      (((∫⁻ ω₁, ∫⁻ ω₂, (f (ω₁, ω₂)).toENNReal ∂κ ω₁ ∂μ) : EReal) -
        ((∫⁻ ω₁, ∫⁻ ω₂, (-f (ω₁, ω₂)).toENNReal ∂κ ω₁ ∂μ) : EReal)) := by
  -- Proof comment: expand the chapter `EReal` integral and apply the nonnegative Tonelli identity
  -- to `f` and to `-f`.
  rw [erealIntegral_spec]
  rw [tonelli_transition_kernel (μ := μ) (κ := κ) hκ hf.1,
    tonelli_transition_kernel (μ := μ) (κ := κ) hκ hf.1.neg]

end
