/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Definition_8_28

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {E : Type v} [mE : MeasurableSpace E]

-- Proof sketch: a regular conditional distribution gives a disintegration of the joint law of
-- `(id, X)` over `P.trim hm`. Apply the conditional-expectation characterization
-- `ae_eq_condExp_of_forall_setIntegral_eq` to the kernel integral
-- `ω ↦ ∫ x, f x ∂κ ω`, and verify the defining set-integral identity via that disintegration.
/-- Theorem 8.38: if `κ` is a regular conditional distribution of `X` given the sub-σ-algebra
`m`, then the conditional expectation of `f ∘ X` given `m` is almost everywhere the integral of
`f` against `κ`. -/
theorem condExp_ae_eq_integral_regular_conditional_distribution
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω)
    (X : Ω → E) (κ : Kernel[m, mE] Ω E) (hκ : IsRegularCondDistrib P m X κ)
    {f : E → ℝ} (hf : Measurable f) (hf_int : Integrable (fun ω ↦ f (X ω)) P) :
    P[fun ω ↦ f (X ω) | m] =ᵐ[P] fun ω ↦ ∫ x, f x ∂κ ω := by
  letI : IsRegularCondDistrib P m X κ := hκ
  let hm : m ≤ mΩ := hκ.le_ambient
  let hX : @Measurable Ω E mΩ mE X := hκ.measurable_Y
  have h_id : Measurable[mΩ, m] (fun ω : Ω ↦ ω) := by
    change m ≤ mΩ
    exact hm
  have h_id_ae : AEMeasurable (fun ω : Ω ↦ ω) P := h_id.aemeasurable
  have hX_ae : AEMeasurable X P := hX.aemeasurable
  let g : Ω → ℝ := fun ω ↦ ∫ x, f x ∂κ ω
  let ρ : @Measure (Ω × E) (m.prod mE) :=
    @Measure.map Ω (Ω × E) mΩ (m.prod mE) (fun ω ↦ (ω, X ω)) P
  have hρ_fst : ρ.fst = P.trim hm := by
    ext s hs
    rw [Measure.fst_apply hs, Measure.map_apply (h_id.prodMk hX) (measurable_fst hs),
      ← Set.prod_univ, Set.mk_preimage_prod, trim_measurableSet_eq hm hs]
    simp
  have hρ : P.trim hm ⊗ₘ κ = ρ := by
    letI : ρ.IsCondKernel κ := by
      change ((@Measure.map Ω (Ω × E) mΩ (m.prod mE) (fun ω ↦ (ω, X ω)) P).IsCondKernel κ)
      infer_instance
    calc
      P.trim hm ⊗ₘ κ = ρ.fst ⊗ₘ κ := by rw [hρ_fst]
      _ = ρ := by simpa using ρ.disintegrate κ
  have hg_meas : StronglyMeasurable[m] g := by
    simpa [g] using hf.stronglyMeasurable.integral_kernel
  have hρ_int : Integrable (fun p : Ω × E ↦ f p.2) ρ := by
    simpa [ρ] using
      (@integrable_map_measure Ω ℝ mΩ P _ _ (Ω × E) (m.prod mE) (fun ω ↦ (ω, X ω))
        (fun p : Ω × E ↦ f p.2) ((hf.comp measurable_snd).aestronglyMeasurable)
        (h_id_ae.prodMk hX_ae)).2 hf_int
  have hcomp_int : Integrable (fun p : Ω × E ↦ f p.2) (P.trim hm ⊗ₘ κ) := by
    simpa [hρ] using hρ_int
  have hg_trim : Integrable g (P.trim hm) := by
    simpa [g] using hcomp_int.integral_compProd
  have hg : Integrable g P := integrable_of_integrable_trim hm hg_trim
  have hg_eq :
      ∀ s : Set Ω, MeasurableSet[m] s → P s < ⊤ → ∫ ω in s, g ω ∂P = ∫ ω in s, f (X ω) ∂P := by
    intro s hs hPs
    calc
      ∫ ω in s, g ω ∂P = ∫ ω in s, g ω ∂P.trim hm := by
        rw [setIntegral_trim hm hg_meas hs]
      _ = ∫ p in s ×ˢ Set.univ, f p.2 ∂(P.trim hm ⊗ₘ κ) := by
        symm
        simpa [g] using
          (Measure.setIntegral_compProd hs MeasurableSet.univ hcomp_int.integrableOn)
      _ = ∫ p in s ×ˢ Set.univ, f p.2 ∂ρ := by
        simp [hρ]
      _ = ∫ ω in (fun ω ↦ (ω, X ω)) ⁻¹' (s ×ˢ Set.univ), f ((ω, X ω)).2 ∂P := by
        simpa [ρ] using
          (@setIntegral_map Ω ℝ mΩ _ _ P (Ω × E) (m.prod mE) (fun ω ↦ (ω, X ω))
            (fun p : Ω × E ↦ f p.2) (s ×ˢ Set.univ) (hs.prod MeasurableSet.univ)
            ((hf.comp measurable_snd).aestronglyMeasurable)
            (h_id_ae.prodMk hX_ae))
      _ = ∫ ω in s, f (X ω) ∂P := by
        simp [Set.mk_preimage_prod]
  exact (ae_eq_condExp_of_forall_setIntegral_eq hm hf_int
    (fun s hs hPs ↦ hg.integrableOn) hg_eq hg_meas.aestronglyMeasurable).symm
