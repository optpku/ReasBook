/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Example_5_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Exercise_3_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory NNReal unitInterval

noncomputable section

universe u

/-- Helper for Example 16.2: the canonical characteristic function attached to the Gaussian-over-
`√Gamma` ratio law, written as the Gamma average of the conditional Gaussian characteristic
functions. -/
noncomputable def gaussianOverSqrtGammaCFP (σ2 : ℝ≥0) (θ r : ℝ) : ℝ → ℂ :=
  fun t ↦ ∫ y, charFun (gaussianReal (0 : ℝ) σ2) (t / Real.sqrt y) ∂(gammaMeasure r θ)

/-- Helper for Example 16.2: the product Gaussian/Gamma law is a probability measure whenever the
Gamma factor is normalized. -/
private theorem isProbabilityMeasure_gaussianOverSqrtGammaProd
    (σ2 : ℝ≥0) (θ r : ℝ) (hθ : 0 < θ) (hr : 0 < r) :
    IsProbabilityMeasure
      (((gaussianReal (0 : ℝ) σ2).prod (gammaMeasure r θ)) : Measure (ℝ × ℝ)) := by
  -- Proof comment: the Gaussian marginal is always a probability measure, and the Gamma marginal
  -- becomes one under the positivity hypotheses.
  letI : IsProbabilityMeasure (gammaMeasure r θ) := isProbabilityMeasure_gammaMeasure hr hθ
  infer_instance

/-- Helper for Example 16.2: the ratio map on the product Gaussian/Gamma space is a.e.
measurable. -/
private lemma gaussianOverSqrtGammaRatio_aemeasurable
    (σ2 : ℝ≥0) (θ r : ℝ) :
    AEMeasurable (fun z : ℝ × ℝ ↦ z.1 / Real.sqrt z.2)
      (((gaussianReal (0 : ℝ) σ2).prod (gammaMeasure r θ)) : Measure (ℝ × ℝ)) := by
  -- Proof comment: assemble the ratio from the measurable coordinate projections, `sqrt`, and
  -- division.
  simpa using measurable_fst.aemeasurable.div measurable_snd.aemeasurable.sqrt

/-- Helper for Example 16.2: the canonical owner law of the ratio `G / √Γ`, where
`G ∼ N(0, σ²)` and `Γ ∼ Γ_{θ,r}` are independent. -/
noncomputable def gaussianOverSqrtGammaLaw
    (σ2 : ℝ≥0) (θ r : ℝ) (hθ : 0 < θ) (hr : 0 < r) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    ⟨((gaussianReal (0 : ℝ) σ2).prod (gammaMeasure r θ)),
      isProbabilityMeasure_gaussianOverSqrtGammaProd σ2 θ r hθ hr⟩
    (gaussianOverSqrtGammaRatio_aemeasurable σ2 θ r)

/-- Helper for Example 16.2: the mapped ratio law has the canonical characteristic function
`gaussianOverSqrtGammaCFP`. -/
theorem ratioGaussianSqrtGamma_map_charFun_eq
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hZ : AEMeasurable (fun ω ↦ X ω / Real.sqrt (Y ω)) P)
    (hXY : IndepFun X Y P) (σ2 : ℝ≥0) (θ r : ℝ)
    (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (hX : HasLaw X (gaussianReal (0 : ℝ) σ2) P)
    (hY : HasLaw Y (gammaMeasure r θ) P) :
    ∀ t : ℝ,
      charFun (((ProbabilityMeasure.map ⟨P, inferInstance⟩ hZ : ProbabilityMeasure ℝ) : Measure ℝ))
        t = gaussianOverSqrtGammaCFP σ2 θ r t := by
  letI : IsProbabilityMeasure (gammaMeasure r θ) := isProbabilityMeasure_gammaMeasure hr hθ
  have hJoint :
      HasLaw (fun ω ↦ (X ω, Y ω))
        ((gaussianReal (0 : ℝ) σ2).prod (gammaMeasure r θ)) P := by
    -- Proof comment: independence upgrades the marginal laws to the product law of the pair.
    refine ⟨hX.aemeasurable.prodMk hY.aemeasurable, ?_⟩
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY,
      hX.map_eq, hY.map_eq]
  intro t
  let f : ℝ × ℝ → ℂ := fun z ↦ Complex.exp (t * (z.1 / Real.sqrt z.2) * Complex.I)
  have hf : AEStronglyMeasurable f
      (((gaussianReal (0 : ℝ) σ2).prod (gammaMeasure r θ)) : Measure (ℝ × ℝ)) := by
    -- Proof comment: the product-space integrand is a measurable exponential of the ratio map.
    fun_prop
  have hInt : Integrable f (((gaussianReal (0 : ℝ) σ2).prod (gammaMeasure r θ)) :
      Measure (ℝ × ℝ)) := by
    -- Proof comment: the complex exponential is uniformly bounded by `1`, so Fubini applies.
    refine Integrable.of_bound hf 1 ?_
    filter_upwards with z
    simp [f, Complex.norm_exp]
  have hmap :
      (((ProbabilityMeasure.map ⟨P, inferInstance⟩ hZ : ProbabilityMeasure ℝ) : Measure ℝ)) =
        P.map (fun ω ↦ X ω / Real.sqrt (Y ω)) := by
    simpa using (ProbabilityMeasure.toMeasure_map ⟨P, inferInstance⟩ hZ)
  calc
    charFun (((ProbabilityMeasure.map ⟨P, inferInstance⟩ hZ : ProbabilityMeasure ℝ) : Measure ℝ)) t
        = ∫ ω, Complex.exp (t * (X ω / Real.sqrt (Y ω)) * Complex.I) ∂P := by
            -- Proof comment: expand the characteristic function of the pushed-forward ratio law.
            rw [hmap, charFun_apply_real]
            rw [integral_map hZ]
            · refine integral_congr_ae ?_
              filter_upwards with ω
              simp
            · fun_prop
    _ = ∫ z, f z ∂(((gaussianReal (0 : ℝ) σ2).prod (gammaMeasure r θ)) : Measure (ℝ × ℝ)) := by
          -- Proof comment: replace the ambient random variables by their joint product law.
          simpa [Function.comp, f] using hJoint.integral_comp hf
    _ = ∫ y, ∫ x, f (x, y) ∂(gaussianReal (0 : ℝ) σ2) ∂(gammaMeasure r θ) := by
          -- Proof comment: separate the product-law integral into iterated Gaussian/Gamma
          -- integrals.
          simpa using integral_prod_symm f hInt
    _ = ∫ y, charFun (gaussianReal (0 : ℝ) σ2) (t / Real.sqrt y) ∂(gammaMeasure r θ) := by
          -- Proof comment: for each Gamma value, the inner integral is exactly the Gaussian
          -- characteristic function at the scaled frequency.
          refine integral_congr_ae ?_
          filter_upwards with y
          rw [charFun_apply_real]
          congr 1
          funext x
          simp [f]
          ring
    _ = gaussianOverSqrtGammaCFP σ2 θ r t := by
          rfl

/-- Helper for Example 16.2: the canonical owner law `gaussianOverSqrtGammaLaw` has characteristic
function `gaussianOverSqrtGammaCFP`. -/
theorem gaussianOverSqrtGammaLaw_charFun_eq
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r) :
    ∀ t : ℝ,
      charFun (((gaussianOverSqrtGammaLaw σ2 θ r hθ hr : ProbabilityMeasure ℝ) : Measure ℝ)) t =
        gaussianOverSqrtGammaCFP σ2 θ r t := by
  let P : Measure (ℝ × ℝ) := ((gaussianReal (0 : ℝ) σ2).prod (gammaMeasure r θ))
  letI : IsProbabilityMeasure (gammaMeasure r θ) := isProbabilityMeasure_gammaMeasure hr hθ
  letI : IsProbabilityMeasure P := isProbabilityMeasure_gaussianOverSqrtGammaProd σ2 θ r hθ hr
  have hZ : AEMeasurable (fun z : ℝ × ℝ ↦ z.1 / Real.sqrt z.2) P := by
    -- Proof comment: the owner law uses the ratio map on the canonical product space.
    simpa [P] using gaussianOverSqrtGammaRatio_aemeasurable σ2 θ r
  have hXY : IndepFun (fun z : ℝ × ℝ ↦ z.1) (fun z : ℝ × ℝ ↦ z.2) P := by
    -- Proof comment: the product measure makes the two coordinate projections independent.
    simpa [P] using
      (ProbabilityTheory.indepFun_prod
        (μ := gaussianReal (0 : ℝ) σ2) (ν := gammaMeasure r θ)
        (X := id) (Y := id) measurable_id measurable_id)
  have hX : HasLaw (fun z : ℝ × ℝ ↦ z.1) (gaussianReal (0 : ℝ) σ2) P := by
    -- Proof comment: the first coordinate of the canonical product law has the Gaussian marginal.
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    simpa [P] using
      (Measure.map_fst_prod
        (μ := gaussianReal (0 : ℝ) σ2) (ν := gammaMeasure r θ))
  have hY : HasLaw (fun z : ℝ × ℝ ↦ z.2) (gammaMeasure r θ) P := by
    -- Proof comment: the second coordinate of the canonical product law has the Gamma marginal.
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    simpa [P] using
      (Measure.map_snd_prod
        (μ := gaussianReal (0 : ℝ) σ2) (ν := gammaMeasure r θ))
  intro t
  -- Proof comment: specialize the general mapped-law characteristic-function computation to the
  -- canonical product model.
  simpa [gaussianOverSqrtGammaLaw, P] using
    ratioGaussianSqrtGamma_map_charFun_eq
      (P := P) (X := fun z : ℝ × ℝ ↦ z.1) (Y := fun z : ℝ × ℝ ↦ z.2)
      hZ hXY σ2 θ r hσ2 hθ hr hX hY t

/-- Helper for Example 16.2: the canonical Gaussian-over-`√Gamma` function is itself a
characteristic function, realized on the product Gaussian/Gamma space. -/
theorem gaussianOverSqrtGammaCFP_isCFP
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r) :
    IsCFP (gaussianOverSqrtGammaCFP σ2 θ r) := by
  refine ⟨gaussianOverSqrtGammaLaw σ2 θ r hθ hr, ?_⟩
  -- Proof comment: the new owner law packages the product-space construction once and for all.
  funext t
  exact gaussianOverSqrtGammaLaw_charFun_eq σ2 θ r hσ2 hθ hr t
