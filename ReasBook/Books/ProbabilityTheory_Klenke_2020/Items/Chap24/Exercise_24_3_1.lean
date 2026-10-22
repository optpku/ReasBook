/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The two-parameter Dirichlet law on pairs, obtained by normalizing two independent
unit-rate Gamma coordinates with shapes `θ₁` and `θ₂`. -/
def dirichletPairMeasure (θ₁ θ₂ : ℝ) : Measure (Fin 2 → ℝ) :=
  (Measure.pi fun i : Fin 2 ↦ gammaMeasure (![θ₁, θ₂] i) 1).map
    (fun y i ↦ y i / ∑ j, y j)

-- Proof sketch: unfold `dirichletPairMeasure`; it is defined as the pushforward of the product
-- Gamma law under normalization by the total mass.
/-- Unfolding `dirichletPairMeasure θ₁ θ₂` gives the normalized-Gamma pushforward formula for the
two-parameter Dirichlet law. -/
theorem dirichletPairMeasure_def (θ₁ θ₂ : ℝ) :
    dirichletPairMeasure θ₁ θ₂ =
      (Measure.pi fun i : Fin 2 ↦ gammaMeasure (![θ₁, θ₂] i) 1).map
        (fun y i ↦ y i / ∑ j, y j) := by
  -- Proof comment: this theorem is just the defining equation of `dirichletPairMeasure`.
  rfl

/-- Helper for Exercise 24.3.1: a unit-rate Gamma variable is almost surely strictly positive. -/
theorem ae_pos_gammaMeasure_unitRate (a : ℝ) (_ha : 0 < a) :
    ∀ᵐ x ∂ gammaMeasure a 1, 0 < x := by
  have hnonneg : ∀ᵐ x ∂ gammaMeasure a 1, 0 ≤ x := by
    rw [gammaMeasure, ae_withDensity_iff (by
      simpa [gammaPDF] using ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a 1))]
    filter_upwards with x hx
    -- Proof comment: the Gamma density vanishes on the negative half-line.
    by_contra hx_neg
    exact hx (gammaPDF_of_neg (lt_of_not_ge hx_neg))
  have hsingleton : gammaMeasure a 1 ({0} : Set ℝ) = 0 := by
    -- Proof comment: Gamma laws are absolutely continuous with respect to Lebesgue measure.
    rw [gammaMeasure, withDensity_apply _ (measurableSet_singleton 0)]
    simp
  have hne_zero : ∀ᵐ x ∂ gammaMeasure a 1, x ≠ 0 := by
    rw [ae_iff]
    simpa using hsingleton
  -- Proof comment: combine nonnegativity with the fact that `0` is a null event.
  filter_upwards [hnonneg, hne_zero] with x hx_nonneg hx_ne
  exact lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)

/-- Helper for Exercise 24.3.1: the Dirichlet pair law is the pushforward of the Gamma-product
pair law under the pairwise normalization map. -/
theorem dirichletPairMeasure_eq_map_gammaPairNormalize
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    dirichletPairMeasure θ₁ θ₂ =
      ((gammaMeasure θ₁ 1).prod (gammaMeasure θ₂ 1)).map
        (fun p : ℝ × ℝ ↦ ![p.1 / (p.1 + p.2), p.2 / (p.1 + p.2)]) := by
  have hnormalize :
      (fun y : Fin 2 → ℝ ↦ fun i ↦ y i / ∑ j, y j) =
        (fun y : Fin 2 → ℝ ↦ ![y 0 / (y 0 + y 1), y 1 / (y 0 + y 1)]) := by
    funext y
    ext i
    fin_cases i <;> simp [Fin.sum_univ_two]
  have hbridge :
      (fun y : Fin 2 → ℝ ↦ ![y 0 / (y 0 + y 1), y 1 / (y 0 + y 1)]) =
        (fun p : ℝ × ℝ ↦ ![p.1 / (p.1 + p.2), p.2 / (p.1 + p.2)]) ∘
          MeasurableEquiv.finTwoArrow := by
    funext y
    simp [Function.comp]
  have hpairNormalize_meas :
      Measurable (fun p : ℝ × ℝ ↦
        (![(p.1 / (p.1 + p.2)), (p.2 / (p.1 + p.2))] : Fin 2 → ℝ)) := by
    rw [measurable_pi_iff]
    intro i
    fin_cases i
    · simpa using measurable_fst.div (measurable_fst.add measurable_snd)
    · simpa using measurable_snd.div (measurable_fst.add measurable_snd)
  have hpi :
      (Measure.pi fun i : Fin 2 ↦ gammaMeasure (![θ₁, θ₂] i) 1) =
        Measure.pi ![gammaMeasure θ₁ 1, gammaMeasure θ₂ 1] := by
    congr 1
    ext i
    fin_cases i <;> rfl
  letI : IsProbabilityMeasure (gammaMeasure θ₁ 1) :=
    isProbabilityMeasure_gammaMeasure hθ₁ zero_lt_one
  letI : IsProbabilityMeasure (gammaMeasure θ₂ 1) :=
    isProbabilityMeasure_gammaMeasure hθ₂ zero_lt_one
  -- Proof comment: rewrite the `Fin 2` Gamma product as an `ℝ × ℝ` product via
  -- `MeasurableEquiv.finTwoArrow`, then identify the normalization map on pairs.
  calc
    dirichletPairMeasure θ₁ θ₂
        = (Measure.pi ![gammaMeasure θ₁ 1, gammaMeasure θ₂ 1]).map
            (fun y : Fin 2 → ℝ ↦ fun i ↦ y i / ∑ j, y j) := by
          rw [dirichletPairMeasure_def, hpi]
    _ = (Measure.pi ![gammaMeasure θ₁ 1, gammaMeasure θ₂ 1]).map
          (fun y : Fin 2 → ℝ ↦ ![y 0 / (y 0 + y 1), y 1 / (y 0 + y 1)]) := by
          rw [Measure.map_congr (Filter.EventuallyEq.of_eq hnormalize)]
    _ = (Measure.pi ![gammaMeasure θ₁ 1, gammaMeasure θ₂ 1]).map
          ((fun p : ℝ × ℝ ↦ ![p.1 / (p.1 + p.2), p.2 / (p.1 + p.2)]) ∘
            MeasurableEquiv.finTwoArrow) := by
          rw [Measure.map_congr (Filter.EventuallyEq.of_eq hbridge)]
    _ = ((Measure.pi ![gammaMeasure θ₁ 1, gammaMeasure θ₂ 1]).map
          MeasurableEquiv.finTwoArrow).map
          (fun p : ℝ × ℝ ↦ ![p.1 / (p.1 + p.2), p.2 / (p.1 + p.2)]) := by
          rw [← Measure.map_map hpairNormalize_meas MeasurableEquiv.finTwoArrow.measurable]
    _ = ((gammaMeasure θ₁ 1).prod (gammaMeasure θ₂ 1)).map
          (fun p : ℝ × ℝ ↦ ![p.1 / (p.1 + p.2), p.2 / (p.1 + p.2)]) := by
          rw [(measurePreserving_finTwoArrow_vec (gammaMeasure θ₁ 1) (gammaMeasure θ₂ 1)).map_eq]

/-- Helper for Exercise 24.3.1: under the canonical `beta × gamma` product source, the first
coordinate has the Beta law. -/
theorem betaGammaProdSource_fst_hasLaw
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    HasLaw Prod.fst (betaMeasure θ₁ θ₂)
      ((betaMeasure θ₁ θ₂).prod (gammaMeasure (θ₁ + θ₂) 1)) := by
  letI : IsProbabilityMeasure (gammaMeasure (θ₁ + θ₂) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos hθ₁ hθ₂) zero_lt_one
  -- Proof comment: on a product source, the first projection preserves the first factor.
  exact
    (measurePreserving_fst
      (μ := betaMeasure θ₁ θ₂) (ν := gammaMeasure (θ₁ + θ₂) 1)).hasLaw

/-- Helper for Exercise 24.3.1: under the canonical `beta × gamma` product source, the second
coordinate has the Gamma law with shape `θ₁ + θ₂`. -/
theorem betaGammaProdSource_snd_hasLaw
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    HasLaw Prod.snd (gammaMeasure (θ₁ + θ₂) 1)
      ((betaMeasure θ₁ θ₂).prod (gammaMeasure (θ₁ + θ₂) 1)) := by
  letI : IsProbabilityMeasure (betaMeasure θ₁ θ₂) := isProbabilityMeasureBeta hθ₁ hθ₂
  letI : IsProbabilityMeasure (gammaMeasure (θ₁ + θ₂) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos hθ₁ hθ₂) zero_lt_one
  -- Proof comment: the second projection likewise preserves the second factor of the product law.
  exact
    (measurePreserving_snd
      (μ := betaMeasure θ₁ θ₂) (ν := gammaMeasure (θ₁ + θ₂) 1)).hasLaw

/-- Helper for Exercise 24.3.1: the canonical Beta and Gamma coordinates are independent under
their product source measure. -/
theorem betaGammaProdSource_indepFun
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    IndepFun Prod.fst Prod.snd
      ((betaMeasure θ₁ θ₂).prod (gammaMeasure (θ₁ + θ₂) 1)) := by
  letI : IsProbabilityMeasure (betaMeasure θ₁ θ₂) := isProbabilityMeasureBeta hθ₁ hθ₂
  letI : IsProbabilityMeasure (gammaMeasure (θ₁ + θ₂) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos hθ₁ hθ₂) zero_lt_one
  -- Proof comment: product measures make the two coordinate projections independent.
  simpa using
    (indepFun_prod (μ := betaMeasure θ₁ θ₂) (ν := gammaMeasure (θ₁ + θ₂) 1)
      measurable_id measurable_id :
      IndepFun (fun p : ℝ × ℝ ↦ p.1) (fun p : ℝ × ℝ ↦ p.2)
        ((betaMeasure θ₁ θ₂).prod (gammaMeasure (θ₁ + θ₂) 1)))

/-- Helper for Exercise 24.3.1: the Beta/Gamma splitting map
`(b, z) ↦ (bz, (1 - b)z)`. -/
private def betaGammaSplit (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * p.2, (1 - p.1) * p.2)

/-- Helper for Exercise 24.3.1: the inverse ratio/sum map
`(x, y) ↦ (x / (x + y), x + y)`. -/
private def gammaPairRatioSum (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 / (p.1 + p.2), p.1 + p.2)

/-- Helper for Exercise 24.3.1: the open strip supporting the canonical `beta × gamma` source
measure. -/
private def betaGammaStrip : Set (ℝ × ℝ) :=
  Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioi 0

/-- Helper for Exercise 24.3.1: the open positive quadrant supporting the Gamma-pair target
measure. -/
private def gammaQuadrant : Set (ℝ × ℝ) :=
  Set.Ioi (0 : ℝ) ×ˢ Set.Ioi 0

/-- Helper for Exercise 24.3.1: the ambient Lebesgue product measure on `ℝ × ℝ`. -/
private def planeMeasure : Measure (ℝ × ℝ) :=
  (volume : Measure ℝ).prod (volume : Measure ℝ)

/-- Helper for Exercise 24.3.1: the raw `beta × gamma` density before restricting to the open
strip support. -/
private def betaGammaSourceDensity (θ₁ θ₂ : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  betaPDF θ₁ θ₂ p.1 * gammaPDF (θ₁ + θ₂) 1 p.2

/-- Helper for Exercise 24.3.1: the raw Gamma-pair density before restricting to the positive
quadrant support. -/
private def gammaPairTargetDensity (θ₁ θ₂ : ℝ) (q : ℝ × ℝ) : ℝ≥0∞ :=
  gammaPDF θ₁ 1 q.1 * gammaPDF θ₂ 1 q.2

/-- Helper for Exercise 24.3.1: the Beta density is measurable as an `ℝ≥0∞`-valued function. -/
private lemma measurableBetaPDF (θ₁ θ₂ : ℝ) : Measurable (betaPDF θ₁ θ₂) := by
  -- Proof comment: `betaPDF` is the `ENNReal.ofReal` lift of the measurable real-valued pdf.
  simpa [betaPDF] using ENNReal.measurable_ofReal.comp (measurable_betaPDFReal θ₁ θ₂)

/-- Helper for Exercise 24.3.1: the unit-rate Gamma density is measurable as an
`ℝ≥0∞`-valued function. -/
private lemma measurableGammaPDFUnitRate (θ : ℝ) : Measurable (gammaPDF θ 1) := by
  -- Proof comment: `gammaPDF` is likewise the `ENNReal.ofReal` lift of the measurable real-valued
  -- Gamma density.
  simpa [gammaPDF] using ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal θ 1)

/-- Helper for Exercise 24.3.1: on `(0,1) × (0,∞)`, the ratio/sum map is a right inverse to the
Beta/Gamma splitting map. -/
private lemma gammaPairRatioSum_betaGammaSplit
    {p : ℝ × ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioi 0) :
    gammaPairRatioSum (betaGammaSplit p) = p := by
  rcases hp with ⟨hp₁, hp₂⟩
  rcases hp₁ with ⟨hb0, hb1⟩
  have hz : 0 < p.2 := hp₂
  -- Proof comment: positive total mass lets the denominator cancel in the first coordinate.
  ext
  · dsimp [gammaPairRatioSum, betaGammaSplit]
    have hsum : p.1 * p.2 + (1 - p.1) * p.2 = p.2 := by
      ring
    rw [hsum, mul_div_cancel_right₀ p.1 hz.ne']
  · dsimp [gammaPairRatioSum, betaGammaSplit]
    ring

/-- Helper for Exercise 24.3.1: on `(0,∞) × (0,∞)`, the split map is a left inverse to the
ratio/sum map. -/
private lemma betaGammaSplit_gammaPairRatioSum
    {q : ℝ × ℝ} (hq : q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi 0) :
    betaGammaSplit (gammaPairRatioSum q) = q := by
  rcases hq with ⟨hq₁, hq₂⟩
  have hsum : 0 < q.1 + q.2 := add_pos hq₁ hq₂
  -- Proof comment: positive Gamma coordinates make the rational inverse formulas well-defined.
  ext
  · dsimp [gammaPairRatioSum, betaGammaSplit]
    field_simp [hsum.ne']
  · dsimp [gammaPairRatioSum, betaGammaSplit]
    field_simp [hsum.ne']
    ring

/-- Helper for Exercise 24.3.1: the second coordinate vanishes on a `planeMeasure`-null set. -/
private lemma ae_snd_ne_zero_plane : ∀ᵐ p : ℝ × ℝ ∂ planeMeasure, p.2 ≠ 0 := by
  -- Proof comment: the horizontal axis is Lebesgue-null, so it does not affect density rewrites.
  rw [planeMeasure, Measure.ae_prod_iff_ae_ae]
  · refine Filter.Eventually.of_forall ?_
    intro x
    rw [ae_iff]
    simp
  · exact measurable_snd (measurableSet_singleton 0).compl

/-- Helper for Exercise 24.3.1: the first coordinate vanishes on a `planeMeasure`-null set. -/
private lemma ae_fst_ne_zero_plane : ∀ᵐ p : ℝ × ℝ ∂ planeMeasure, p.1 ≠ 0 := by
  -- Proof comment: the vertical axis is also Lebesgue-null, so the target density can be
  -- restricted to the open quadrant without changing the measure.
  change ∀ᵐ p : ℝ × ℝ ∂ ((volume : Measure ℝ).prod volume), p.1 ∈ ({0} : Set ℝ)ᶜ
  rw [Measure.ae_prod_iff_ae_ae (measurable_fst (measurableSet_singleton 0).compl)]
  have hzero : ∀ᵐ x ∂ (volume : Measure ℝ), x ∈ ({0} : Set ℝ)ᶜ := by
    rw [ae_iff]
    simp
  filter_upwards [hzero] with x hx
  exact Filter.Eventually.of_forall fun _ ↦ hx

/-- Helper for Exercise 24.3.1: the canonical `beta × gamma` product law is one `withDensity`
measure over `planeMeasure`, with the support cut down to the open strip. -/
private lemma betaGammaProd_eq_withDensity_strip
    (θ₁ θ₂ : ℝ) :
    ((betaMeasure θ₁ θ₂).prod (gammaMeasure (θ₁ + θ₂) 1)) =
      planeMeasure.withDensity (Set.indicator betaGammaStrip (betaGammaSourceDensity θ₁ θ₂)) := by
  -- Proof comment: rewrite the product measure into one ambient `withDensity`, then remove the
  -- null boundary line `z = 0` and the already-zero Beta boundary outside `(0,1)`.
  rw [betaMeasure, gammaMeasure, planeMeasure,
    prod_withDensity (measurableBetaPDF θ₁ θ₂) (measurableGammaPDFUnitRate (θ₁ + θ₂))]
  apply withDensity_congr_ae
  filter_upwards [ae_snd_ne_zero_plane] with p hp2
  by_cases hmem : p ∈ betaGammaStrip
  · rw [Set.indicator_of_mem hmem]
    simp [betaGammaSourceDensity]
  · rw [Set.indicator_of_notMem hmem]
    rcases lt_or_gt_of_ne hp2 with hp2neg | hp2pos
    · -- Proof comment: on the negative half-line, the Gamma density already vanishes.
      simp [gammaPDF_of_neg hp2neg]
    · -- Proof comment: with `p.2 > 0`, being outside the strip means the Beta coordinate lies
      -- outside `(0,1)`, where the Beta density vanishes.
      by_cases hp1le : p.1 ≤ 0
      · simp [betaPDF_eq_zero_of_nonpos hp1le]
      · have hp1ge : 1 ≤ p.1 := by
          have hp10 : 0 < p.1 := lt_of_not_ge hp1le
          by_cases hp1lt : p.1 < 1
          · exfalso
            exact hmem ⟨⟨hp10, hp1lt⟩, hp2pos⟩
          · exact le_of_not_gt hp1lt
        simp [betaPDF_eq_zero_of_one_le hp1ge]

/-- Helper for Exercise 24.3.1: the Gamma-pair product law is one `withDensity` measure over
`planeMeasure`, with the support cut down to the open quadrant. -/
private lemma gammaPairProd_eq_withDensity_quadrant
    (θ₁ θ₂ : ℝ) :
    ((gammaMeasure θ₁ 1).prod (gammaMeasure θ₂ 1)) =
      planeMeasure.withDensity (Set.indicator gammaQuadrant (gammaPairTargetDensity θ₁ θ₂)) := by
  -- Proof comment: after rewriting the product as one ambient `withDensity`, only the null axes
  -- remain to be removed from the Gamma support.
  rw [gammaMeasure, gammaMeasure, planeMeasure,
    prod_withDensity (measurableGammaPDFUnitRate θ₁) (measurableGammaPDFUnitRate θ₂)]
  apply withDensity_congr_ae
  filter_upwards [ae_fst_ne_zero_plane, ae_snd_ne_zero_plane] with q hq1 hq2
  by_cases hmem : q ∈ gammaQuadrant
  · rw [Set.indicator_of_mem hmem]
    simp [gammaPairTargetDensity]
  · rw [Set.indicator_of_notMem hmem]
    rcases lt_or_gt_of_ne hq1 with hq1neg | hq1pos
    · -- Proof comment: if the first coordinate is negative, the first Gamma density is zero.
      simp [gammaPDF_of_neg hq1neg]
    · -- Proof comment: otherwise the second coordinate must be negative, since both coordinates are
      -- nonzero and the point lies outside the open quadrant.
      rcases lt_or_gt_of_ne hq2 with hq2neg | hq2pos
      · simp [gammaPDF_of_neg hq2neg]
      · exfalso
        exact hmem ⟨hq1pos, hq2pos⟩

/-- Helper for Exercise 24.3.1: the split map is injective on the open strip because
`gammaPairRatioSum` is a right inverse there. -/
private lemma betaGammaSplit_injOn_strip : Set.InjOn betaGammaSplit betaGammaStrip := by
  -- Proof comment: apply the explicit inverse `gammaPairRatioSum` to both sides of an equality on
  -- the strip.
  intro p hp q hq hpq
  calc
    p = gammaPairRatioSum (betaGammaSplit p) := by
      symm
      exact gammaPairRatioSum_betaGammaSplit hp
    _ = gammaPairRatioSum (betaGammaSplit q) := by rw [hpq]
    _ = q := gammaPairRatioSum_betaGammaSplit hq

/-- Helper for Exercise 24.3.1: the split map sends the open strip exactly onto the positive
quadrant. -/
private lemma betaGammaSplit_image_strip : betaGammaSplit '' betaGammaStrip = gammaQuadrant := by
  -- Proof comment: positivity of both split coordinates gives the forward inclusion, and the
  -- explicit inverse `gammaPairRatioSum` gives the reverse inclusion.
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨⟨hb0, hb1⟩, hz⟩
    constructor
    · exact mul_pos hb0 hz
    · exact mul_pos (sub_pos.mpr hb1) hz
  · intro hq
    refine ⟨gammaPairRatioSum q, ?_, betaGammaSplit_gammaPairRatioSum hq⟩
    rcases hq with ⟨hq₁, hq₂⟩
    have hsum : 0 < q.1 + q.2 := add_pos hq₁ hq₂
    constructor
    · constructor
      · exact div_pos hq₁ hsum
      · have hlt : q.1 < q.1 + q.2 := lt_add_of_pos_right q.1 hq₂
        have hfrac :
            q.1 / (q.1 + q.2) < (q.1 + q.2) / (q.1 + q.2) :=
          div_lt_div_of_pos_right hlt hsum
        simpa [hsum.ne'] using hfrac
    · exact hsum

/-- Helper for Exercise 24.3.1: the explicit derivative of the split map. -/
private def betaGammaSplitFDeriv (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearMap.prod
    (p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ)
    (-(p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) + (1 - p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- Helper for Exercise 24.3.1: the split map has the expected derivative everywhere, hence in
particular on the open strip. -/
private lemma betaGammaSplit_hasFDerivAt (p : ℝ × ℝ) :
    HasFDerivAt betaGammaSplit (betaGammaSplitFDeriv p) p := by
  have hMul :
      HasFDerivAt (fun q : ℝ × ℝ ↦ q.1 * q.2)
        (p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
    -- Proof comment: differentiate the first split coordinate `q₁ q₂` by the product rule.
    simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using
      ((hasFDerivAt_fst (p := p)).mul (hasFDerivAt_snd (p := p)))
  have hOneMinus :
      HasFDerivAt (fun q : ℝ × ℝ ↦ 1 - q.1) (-ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
    -- Proof comment: the affine factor `1 - q₁` differentiates to `-fst`.
    have hconst :
        HasFDerivAt (fun _ : ℝ × ℝ ↦ (1 : ℝ)) (0 : (ℝ × ℝ) →L[ℝ] ℝ) p :=
      hasFDerivAt_const (1 : ℝ) p
    simpa using hconst.sub (hasFDerivAt_fst (p := p))
  have hSecondRaw :
      HasFDerivAt (Prod.snd * fun q : ℝ × ℝ ↦ 1 - q.1)
        (-(p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) + (1 - p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
    -- Proof comment: differentiate the second split coordinate `q₂ * (1 - q₁)` by the product
    -- rule in the spelling that Lean produces directly.
    simpa using ((hasFDerivAt_snd (p := p)).mul hOneMinus)
  have hPair :
      HasFDerivAt (fun q : ℝ × ℝ ↦ (q.1 * q.2, q.2 * (1 - q.1)))
        ((p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
          (-(p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) +
            (1 - p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    hMul.prodMk hSecondRaw
  show HasFDerivAt (fun q : ℝ × ℝ ↦ (q.1 * q.2, (1 - q.1) * q.2)) (betaGammaSplitFDeriv p) p
  -- Proof comment: combine the two coordinate derivatives into the derivative of the pair-valued
  -- split map.
  simpa [betaGammaSplitFDeriv, mul_comm, neg_smul] using hPair

/-- Helper for Exercise 24.3.1: the strip-restricted split map uses the same derivative, since the
ambient derivative already exists. -/
private lemma betaGammaSplit_hasFDerivWithinAt
    {p : ℝ × ℝ} (_hp : p ∈ betaGammaStrip) :
    HasFDerivWithinAt betaGammaSplit (betaGammaSplitFDeriv p) betaGammaStrip p := by
  -- Proof comment: once the ambient derivative is known, the within-derivative is immediate.
  exact (betaGammaSplit_hasFDerivAt p).hasFDerivWithinAt

/-- Helper for Exercise 24.3.1: a fixed basis on `ℝ × ℝ` used to compute the Jacobian
determinant of the split derivative. -/
private def pairBasis : Module.Basis (Fin 2) ℝ (ℝ × ℝ) :=
  (Pi.basisFun ℝ (Fin 2)).map (LinearEquiv.finTwoArrow ℝ ℝ)

/-- Helper for Exercise 24.3.1: the derivative matrix of the split map in the standard pair basis
is the textbook `2 × 2` Jacobian matrix. -/
private lemma betaGammaSplitFDeriv_matrix (p : ℝ × ℝ) :
    LinearMap.toMatrix pairBasis pairBasis (betaGammaSplitFDeriv p).toLinearMap =
      !![p.2, p.1; -p.2, 1 - p.1] := by
  -- Proof comment: evaluate the derivative on the two basis vectors and read off the resulting
  -- matrix entries.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, pairBasis, betaGammaSplitFDeriv, Pi.basisFun_repr,
      LinearEquiv.finTwoArrow]

/-- Helper for Exercise 24.3.1: the Jacobian determinant of the split derivative is exactly the
second source coordinate. -/
private lemma betaGammaSplitFDeriv_det (p : ℝ × ℝ) :
    (betaGammaSplitFDeriv p).det = p.2 := by
  -- Proof comment: after expressing the derivative in the standard `2 × 2` matrix form, the
  -- determinant reduces to the elementary formula `z (1 - b) - b (-z) = z`.
  change LinearMap.det (betaGammaSplitFDeriv p).toLinearMap = p.2
  rw [← LinearMap.det_toMatrix pairBasis (betaGammaSplitFDeriv p).toLinearMap,
    betaGammaSplitFDeriv_matrix, Matrix.det_fin_two]
  simp
  ring_nf

/-- Helper for Exercise 24.3.1: the split map is measurable because both coordinates are
built from measurable arithmetic operations. -/
private lemma measurable_betaGammaSplit : Measurable betaGammaSplit := by
  -- Proof comment: each split coordinate is a polynomial combination of the pair projections.
  fun_prop

/-- Helper for Exercise 24.3.1: the strip support is measurable. -/
private lemma measurableSet_betaGammaStrip : MeasurableSet betaGammaStrip :=
  measurableSet_Ioo.prod measurableSet_Ioi

/-- Helper for Exercise 24.3.1: the positive quadrant support is measurable. -/
private lemma measurableSet_gammaQuadrant : MeasurableSet gammaQuadrant :=
  measurableSet_Ioi.prod measurableSet_Ioi

/-- Helper for Exercise 24.3.1: points in the open strip are sent into the positive quadrant by
the split map. -/
private lemma betaGammaSplit_mem_quadrant
    {p : ℝ × ℝ} (hp : p ∈ betaGammaStrip) :
    betaGammaSplit p ∈ gammaQuadrant := by
  rcases hp with ⟨⟨hb0, hb1⟩, hz⟩
  -- Proof comment: both split coordinates are positive because `b ∈ (0, 1)` and `z > 0`.
  exact ⟨mul_pos hb0 hz, mul_pos (sub_pos.mpr hb1) hz⟩

/-- Helper for Exercise 24.3.1: on the strip, the `beta × gamma` source density collapses to the
common Gamma-product normal form with the Beta constant already rewritten through `beta`. -/
private lemma betaGammaSourceDensity_eq_of_mem_strip
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    {p : ℝ × ℝ} (hp : p ∈ betaGammaStrip) :
    betaGammaSourceDensity θ₁ θ₂ p =
      ENNReal.ofReal
        ((1 / (Real.Gamma θ₁ * Real.Gamma θ₂)) *
          p.1 ^ (θ₁ - 1) * (1 - p.1) ^ (θ₂ - 1) *
          p.2 ^ (θ₁ + θ₂ - 1) * Real.exp (-p.2)) := by
  rcases hp with ⟨⟨hb0, hb1⟩, hz⟩
  have hBeta_pos : 0 < beta θ₁ θ₂ := beta_pos hθ₁ hθ₂
  have hGammaSum_pos : 0 < Real.Gamma (θ₁ + θ₂) := Real.Gamma_pos_of_pos (add_pos hθ₁ hθ₂)
  have hGammaθ₁_ne : Real.Gamma θ₁ ≠ 0 := (Real.Gamma_pos_of_pos hθ₁).ne'
  have hGammaθ₂_ne : Real.Gamma θ₂ ≠ 0 := (Real.Gamma_pos_of_pos hθ₂).ne'
  have hGammaSum_ne : Real.Gamma (θ₁ + θ₂) ≠ 0 := hGammaSum_pos.ne'
  have hBeta_nonneg :
      0 ≤ (1 / beta θ₁ θ₂) * p.1 ^ (θ₁ - 1) * (1 - p.1) ^ (θ₂ - 1) := by
    have hInv_nonneg : 0 ≤ 1 / beta θ₁ θ₂ := by
      exact one_div_nonneg.mpr hBeta_pos.le
    have hPow_nonneg : 0 ≤ p.1 ^ (θ₁ - 1) := Real.rpow_nonneg (le_of_lt hb0) _
    have hPowOne_nonneg : 0 ≤ (1 - p.1) ^ (θ₂ - 1) := by
      exact Real.rpow_nonneg (sub_nonneg.mpr (le_of_lt hb1)) _
    exact mul_nonneg (mul_nonneg hInv_nonneg hPow_nonneg) hPowOne_nonneg
  have hGamma_nonneg :
      0 ≤ 1 ^ (θ₁ + θ₂) / Real.Gamma (θ₁ + θ₂) * p.2 ^ (θ₁ + θ₂ - 1) * Real.exp (-(1 * p.2)) := by
    have hInv_nonneg : 0 ≤ 1 ^ (θ₁ + θ₂) / Real.Gamma (θ₁ + θ₂) := by
      rw [Real.one_rpow]
      exact one_div_nonneg.mpr hGammaSum_pos.le
    have hPow_nonneg : 0 ≤ p.2 ^ (θ₁ + θ₂ - 1) := Real.rpow_nonneg (le_of_lt hz) _
    have hExp_nonneg : 0 ≤ Real.exp (-(1 * p.2)) := by positivity
    exact mul_nonneg (mul_nonneg hInv_nonneg hPow_nonneg) hExp_nonneg
  have hconst :
      (1 / beta θ₁ θ₂) * (1 ^ (θ₁ + θ₂) / Real.Gamma (θ₁ + θ₂)) =
        1 / (Real.Gamma θ₁ * Real.Gamma θ₂) := by
    -- Proof comment: the Beta normalization constant is already defined as the Gamma ratio.
    rw [beta, Real.one_rpow]
    field_simp [hGammaθ₁_ne, hGammaθ₂_ne, hGammaSum_ne]
  -- Proof comment: rewrite both densities on their positive support and then collapse the
  -- constants to the common Gamma-product normalization.
  rw [betaGammaSourceDensity, betaPDF_of_pos_lt_one hb0 hb1, gammaPDF_of_nonneg hz.le]
  rw [← ENNReal.ofReal_mul hBeta_nonneg]
  congr 1
  calc
    ((1 / beta θ₁ θ₂) * p.1 ^ (θ₁ - 1) * (1 - p.1) ^ (θ₂ - 1)) *
        (1 ^ (θ₁ + θ₂) / Real.Gamma (θ₁ + θ₂) * p.2 ^ (θ₁ + θ₂ - 1) *
          Real.exp (-(1 * p.2)))
      = ((1 / beta θ₁ θ₂) * (1 ^ (θ₁ + θ₂) / Real.Gamma (θ₁ + θ₂))) *
          p.1 ^ (θ₁ - 1) * (1 - p.1) ^ (θ₂ - 1) *
          p.2 ^ (θ₁ + θ₂ - 1) * Real.exp (-p.2) := by
            ring_nf
    _ = ((1 / (Real.Gamma θ₁ * Real.Gamma θ₂)) *
          p.1 ^ (θ₁ - 1) * (1 - p.1) ^ (θ₂ - 1) *
          p.2 ^ (θ₁ + θ₂ - 1) * Real.exp (-p.2)) := by
            rw [hconst]

/-- Helper for Exercise 24.3.1: after composing with the split map, the target Gamma-pair density
has the expected strip normal form before the Jacobian factor is inserted. -/
private lemma gammaPairTargetDensity_split_eq_of_mem_strip
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁)
    {p : ℝ × ℝ} (hp : p ∈ betaGammaStrip) :
    gammaPairTargetDensity θ₁ θ₂ (betaGammaSplit p) =
      ENNReal.ofReal
        ((1 / (Real.Gamma θ₁ * Real.Gamma θ₂)) *
          p.1 ^ (θ₁ - 1) * (1 - p.1) ^ (θ₂ - 1) *
          p.2 ^ (θ₁ + θ₂ - 2) * Real.exp (-p.2)) := by
  rcases hp with ⟨⟨hb0, hb1⟩, hz⟩
  have hb_nonneg : 0 ≤ p.1 := le_of_lt hb0
  have h1b_nonneg : 0 ≤ 1 - p.1 := sub_nonneg.mpr (le_of_lt hb1)
  have hz_nonneg : 0 ≤ p.2 := le_of_lt hz
  have hfirst_nonneg :
      0 ≤ 1 ^ θ₁ / Real.Gamma θ₁ * (p.1 * p.2) ^ (θ₁ - 1) * Real.exp (-(1 * (p.1 * p.2))) := by
    have hInv_nonneg : 0 ≤ 1 ^ θ₁ / Real.Gamma θ₁ := by
      rw [Real.one_rpow]
      exact one_div_nonneg.mpr (Real.Gamma_pos_of_pos hθ₁).le
    have hPow_nonneg : 0 ≤ (p.1 * p.2) ^ (θ₁ - 1) := by positivity
    have hExp_nonneg : 0 ≤ Real.exp (-(1 * (p.1 * p.2))) := by positivity
    exact mul_nonneg (mul_nonneg hInv_nonneg hPow_nonneg) hExp_nonneg
  have hpow :
      p.2 ^ ((θ₁ - 1) + (θ₂ - 1)) = p.2 ^ (θ₁ + θ₂ - 2) := by
    congr 1
    ring
  have hexp :
      Real.exp (-(p.1 * p.2) + -((1 - p.1) * p.2)) = Real.exp (-p.2) := by
    congr 1
    ring
  -- Proof comment: rewrite both Gamma factors on the positive quadrant and factor the `b`, `1-b`,
  -- and `z` powers into the same normal form as the source density.
  change gammaPDF θ₁ 1 (p.1 * p.2) * gammaPDF θ₂ 1 ((1 - p.1) * p.2) =
    ENNReal.ofReal
      ((1 / (Real.Gamma θ₁ * Real.Gamma θ₂)) *
        p.1 ^ (θ₁ - 1) * (1 - p.1) ^ (θ₂ - 1) *
        p.2 ^ (θ₁ + θ₂ - 2) * Real.exp (-p.2))
  rw [gammaPDF_of_nonneg (show 0 ≤ p.1 * p.2 by positivity),
    gammaPDF_of_nonneg (show 0 ≤ (1 - p.1) * p.2 by positivity)]
  rw [← ENNReal.ofReal_mul hfirst_nonneg]
  congr 1
  calc
    (1 ^ θ₁ / Real.Gamma θ₁ * (p.1 * p.2) ^ (θ₁ - 1) * Real.exp (-(1 * (p.1 * p.2)))) *
        (1 ^ θ₂ / Real.Gamma θ₂ * ((1 - p.1) * p.2) ^ (θ₂ - 1) *
          Real.exp (-(1 * ((1 - p.1) * p.2))))
      = ((1 / Real.Gamma θ₁) * (p.1 ^ (θ₁ - 1) * p.2 ^ (θ₁ - 1)) *
            Real.exp (-(p.1 * p.2))) *
          ((1 / Real.Gamma θ₂) * ((1 - p.1) ^ (θ₂ - 1) * p.2 ^ (θ₂ - 1)) *
            Real.exp (-((1 - p.1) * p.2))) := by
              rw [Real.one_rpow, Real.one_rpow, Real.mul_rpow hb_nonneg hz_nonneg,
                Real.mul_rpow h1b_nonneg hz_nonneg]
              simp
    _ = ((1 / (Real.Gamma θ₁ * Real.Gamma θ₂)) *
          p.1 ^ (θ₁ - 1) * (1 - p.1) ^ (θ₂ - 1) *
          (p.2 ^ (θ₁ - 1) * p.2 ^ (θ₂ - 1)) *
          (Real.exp (-(p.1 * p.2)) * Real.exp (-((1 - p.1) * p.2)))) := by
            ring
    _ = ((1 / (Real.Gamma θ₁ * Real.Gamma θ₂)) *
          p.1 ^ (θ₁ - 1) * (1 - p.1) ^ (θ₂ - 1) *
          p.2 ^ ((θ₁ - 1) + (θ₂ - 1)) *
          Real.exp (-(p.1 * p.2) + -((1 - p.1) * p.2))) := by
            rw [← Real.rpow_add hz (θ₁ - 1) (θ₂ - 1), ← Real.exp_add]
    _ = ((1 / (Real.Gamma θ₁ * Real.Gamma θ₂)) *
          p.1 ^ (θ₁ - 1) * (1 - p.1) ^ (θ₂ - 1) *
          p.2 ^ (θ₁ + θ₂ - 2) * Real.exp (-p.2)) := by
            rw [hpow, hexp]

/-- Helper for Exercise 24.3.1: on the strip, the Jacobian-weighted target density agrees exactly
with the source density. -/
private lemma betaGammaWeightedTarget_eq_source_of_mem_strip
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    {p : ℝ × ℝ} (hp : p ∈ betaGammaStrip) :
    ENNReal.ofReal |(betaGammaSplitFDeriv p).det| *
        gammaPairTargetDensity θ₁ θ₂ (betaGammaSplit p) =
      betaGammaSourceDensity θ₁ θ₂ p := by
  have hp' := hp
  rcases hp with ⟨_, hz⟩
  have hz_nonneg : 0 ≤ p.2 := le_of_lt hz
  have hpow :
      p.2 * p.2 ^ (θ₁ + θ₂ - 2) = p.2 ^ (θ₁ + θ₂ - 1) := by
    calc
      p.2 * p.2 ^ (θ₁ + θ₂ - 2)
        = p.2 ^ (1 : ℝ) * p.2 ^ (θ₁ + θ₂ - 2) := by rw [Real.rpow_one]
      _ = p.2 ^ ((1 : ℝ) + (θ₁ + θ₂ - 2)) := by
            rw [← Real.rpow_add hz 1 (θ₁ + θ₂ - 2)]
      _ = p.2 ^ (θ₁ + θ₂ - 1) := by
            congr 1
            ring
  -- Proof comment: once the target density is in strip normal form, the Jacobian determinant adds
  -- the missing factor `z`, turning the target integrand into the source density.
  rw [gammaPairTargetDensity_split_eq_of_mem_strip θ₁ θ₂ hθ₁ hp',
    betaGammaSourceDensity_eq_of_mem_strip θ₁ θ₂ hθ₁ hθ₂ hp',
    betaGammaSplitFDeriv_det, abs_of_pos hz]
  rw [← ENNReal.ofReal_mul hz_nonneg]
  congr 1
  calc
    p.2 *
        ((1 / (Real.Gamma θ₁ * Real.Gamma θ₂)) *
          p.1 ^ (θ₁ - 1) * (1 - p.1) ^ (θ₂ - 1) *
          p.2 ^ (θ₁ + θ₂ - 2) * Real.exp (-p.2))
      = ((1 / (Real.Gamma θ₁ * Real.Gamma θ₂)) *
          p.1 ^ (θ₁ - 1) * (1 - p.1) ^ (θ₂ - 1) *
          (p.2 * p.2 ^ (θ₁ + θ₂ - 2)) * Real.exp (-p.2)) := by
            ring
    _ = ((1 / (Real.Gamma θ₁ * Real.Gamma θ₂)) *
          p.1 ^ (θ₁ - 1) * (1 - p.1) ^ (θ₂ - 1) *
          p.2 ^ (θ₁ + θ₂ - 1) * Real.exp (-p.2)) := by
            rw [hpow]

theorem map_betaGammaSplit_eq_prod_gamma
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    (((betaMeasure θ₁ θ₂).prod (gammaMeasure (θ₁ + θ₂) 1)).map
      (fun p : ℝ × ℝ ↦ (p.1 * p.2, (1 - p.1) * p.2))) =
      (gammaMeasure θ₁ 1).prod (gammaMeasure θ₂ 1) := by
  -- Route correction: the executable local route is to combine the two inverse-support lemmas
  -- above with a Jacobian change-of-variables proof on `betaGammaStrip`.
  have hchange :
      ∀ s : Set (ℝ × ℝ),
        ∫⁻ y in betaGammaSplit '' betaGammaStrip,
            Set.indicator s (gammaPairTargetDensity θ₁ θ₂) y ∂ planeMeasure
          = ∫⁻ x in betaGammaStrip,
              ENNReal.ofReal |(betaGammaSplitFDeriv x).det| *
                Set.indicator s (gammaPairTargetDensity θ₁ θ₂) (betaGammaSplit x)
              ∂ planeMeasure := by
    intro s
    simpa [planeMeasure] using
      MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
        (μ := ((volume : Measure ℝ).prod (volume : Measure ℝ))) (s := betaGammaStrip) (f := betaGammaSplit)
        (f' := betaGammaSplitFDeriv) measurableSet_betaGammaStrip
        (fun x hx ↦ betaGammaSplit_hasFDerivWithinAt hx) betaGammaSplit_injOn_strip
        (Set.indicator s (gammaPairTargetDensity θ₁ θ₂))
  -- Proof comment: rewrite both product measures as ambient `withDensity` measures, apply the
  -- Jacobian formula on the strip, and use the weighted density identity to match the source.
  rw [betaGammaProd_eq_withDensity_strip, gammaPairProd_eq_withDensity_quadrant]
  apply Measure.ext
  intro s hs
  change (Measure.map betaGammaSplit
      (planeMeasure.withDensity (Set.indicator betaGammaStrip (betaGammaSourceDensity θ₁ θ₂)))) s =
    (planeMeasure.withDensity (Set.indicator gammaQuadrant (gammaPairTargetDensity θ₁ θ₂))) s
  rw [Measure.map_apply measurable_betaGammaSplit hs, withDensity_apply _ (hs.preimage measurable_betaGammaSplit),
    withDensity_apply _ hs]
  calc
    ∫⁻ x in betaGammaSplit ⁻¹' s,
        Set.indicator betaGammaStrip (betaGammaSourceDensity θ₁ θ₂) x ∂ planeMeasure
      = ∫⁻ x in betaGammaStrip,
          ENNReal.ofReal |(betaGammaSplitFDeriv x).det| *
            Set.indicator s (gammaPairTargetDensity θ₁ θ₂) (betaGammaSplit x) ∂ planeMeasure := by
            rw [← lintegral_indicator (hs.preimage measurable_betaGammaSplit),
              ← lintegral_indicator measurableSet_betaGammaStrip]
            refine lintegral_congr_ae (Filter.Eventually.of_forall ?_)
            intro x
            by_cases hx : x ∈ betaGammaStrip
            · by_cases hxs : betaGammaSplit x ∈ s
              · simpa [hx, hxs] using
                  (betaGammaWeightedTarget_eq_source_of_mem_strip θ₁ θ₂ hθ₁ hθ₂ hx).symm
              · simp [hx, hxs]
            · simp [hx]
    _ = ∫⁻ y in gammaQuadrant, Set.indicator s (gammaPairTargetDensity θ₁ θ₂) y ∂ planeMeasure := by
          simpa [betaGammaSplit_image_strip] using (hchange s).symm
    _ = ∫⁻ y in s, Set.indicator gammaQuadrant (gammaPairTargetDensity θ₁ θ₂) y ∂ planeMeasure := by
          rw [← lintegral_indicator measurableSet_gammaQuadrant, ← lintegral_indicator hs]
          congr 1
          ext y
          by_cases hyq : y ∈ gammaQuadrant <;> by_cases hys : y ∈ s <;>
            simp [hyq, hys]

/-- Helper for Exercise 24.3.1: the ratio/sum map sends the independent Gamma pair to the
product `betaMeasure θ₁ θ₂ × gammaMeasure (θ₁ + θ₂) 1`. -/
theorem map_gammaPair_toRatioSum_eq_prod_beta_gamma
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    (((gammaMeasure θ₁ 1).prod (gammaMeasure θ₂ 1)).map
      (fun p : ℝ × ℝ ↦ (p.1 / (p.1 + p.2), p.1 + p.2))) =
      (betaMeasure θ₁ θ₂).prod (gammaMeasure (θ₁ + θ₂) 1) := by
  let betaGamma : Measure (ℝ × ℝ) := (betaMeasure θ₁ θ₂).prod (gammaMeasure (θ₁ + θ₂) 1)
  let gammaPair : Measure (ℝ × ℝ) := (gammaMeasure θ₁ 1).prod (gammaMeasure θ₂ 1)
  let split : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1 * p.2, (1 - p.1) * p.2)
  let ratioSum : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1 / (p.1 + p.2), p.1 + p.2)
  letI : IsProbabilityMeasure (betaMeasure θ₁ θ₂) := isProbabilityMeasureBeta hθ₁ hθ₂
  letI : IsProbabilityMeasure (gammaMeasure (θ₁ + θ₂) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos hθ₁ hθ₂) zero_lt_one
  have hsplit_meas : Measurable split := by
    -- Proof comment: the split map is built from measurable arithmetic operations.
    fun_prop
  have hratioSum_meas : Measurable ratioSum := by
    -- Proof comment: the ratio/sum map is likewise measurable on `ℝ × ℝ`.
    fun_prop
  have hratio_split :
      (fun p : ℝ × ℝ ↦ ratioSum (split p)) =ᵐ[betaGamma] fun p ↦ p := by
    have hpos :
        ∀ᵐ z ∂ gammaMeasure (θ₁ + θ₂) 1, 0 < z :=
      ae_pos_gammaMeasure_unitRate (θ₁ + θ₂) (add_pos hθ₁ hθ₂)
    have hMeas :
        MeasurableSet {p : ℝ × ℝ | ratioSum (split p) = p} := by
      exact measurableSet_eq_fun (hratioSum_meas.comp hsplit_meas) measurable_id
    change ∀ᵐ p ∂ betaGamma, ratioSum (split p) = p
    rw [Measure.ae_prod_iff_ae_ae hMeas]
    refine Filter.Eventually.of_forall ?_
    intro b
    filter_upwards [hpos] with z hz
    -- Proof comment: when the Gamma coordinate is strictly positive, `ratioSum` is a right
    -- inverse to the split map.
    ext
    · dsimp [ratioSum, split]
      have hzsum : b * z + (1 - b) * z = z := by
        ring
      rw [hzsum, mul_div_cancel_right₀ b hz.ne']
    · dsimp [ratioSum, split]
      ring
  -- Proof comment: rewrite the Gamma pair measure through the split pushforward and then compose
  -- with the almost-sure inverse relation on the Beta/Gamma source.
  calc
    gammaPair.map ratioSum = (betaGamma.map split).map ratioSum := by
      rw [map_betaGammaSplit_eq_prod_gamma θ₁ θ₂ hθ₁ hθ₂]
    _ = betaGamma.map (ratioSum ∘ split) := by
      rw [Measure.map_map hratioSum_meas hsplit_meas]
    _ = betaGamma.map id := by
      simpa [Function.comp] using (Measure.map_congr hratio_split :
        Measure.map (fun p : ℝ × ℝ ↦ ratioSum (split p)) betaGamma = Measure.map id betaGamma)
    _ = betaGamma := by
      simp

/-- Helper for Exercise 24.3.1: the first Dirichlet coordinate has the `betaMeasure θ₁ θ₂`
law. -/
theorem map_apply_zero_dirichletPairMeasure_eq_beta
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    (dirichletPairMeasure θ₁ θ₂).map (fun z : Fin 2 → ℝ ↦ z 0) = betaMeasure θ₁ θ₂ := by
  let ratioSum : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1 / (p.1 + p.2), p.1 + p.2)
  letI : IsProbabilityMeasure (gammaMeasure (θ₁ + θ₂) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos hθ₁ hθ₂) zero_lt_one
  have hnormalize_meas :
      Measurable (fun p : ℝ × ℝ ↦
        (![(p.1 / (p.1 + p.2)), (p.2 / (p.1 + p.2))] : Fin 2 → ℝ)) := by
    -- Proof comment: the normalization map into `Fin 2 → ℝ` is coordinatewise measurable.
    rw [measurable_pi_iff]
    intro i
    fin_cases i
    · simpa using measurable_fst.div (measurable_fst.add measurable_snd)
    · simpa using measurable_snd.div (measurable_fst.add measurable_snd)
  have hratioSum_meas : Measurable ratioSum := by
    -- Proof comment: the scalar ratio and the total sum are both measurable.
    fun_prop
  have hcoord :
      (fun p : ℝ × ℝ ↦ p.1 / (p.1 + p.2)) = Prod.fst ∘ ratioSum := by
    -- Proof comment: the first normalized coordinate is the first projection after `ratioSum`.
    funext p
    rfl
  -- Proof comment: rewrite the Dirichlet pair as the normalized Gamma pair, convert the first
  -- coordinate into the first projection after `ratioSum`, and then project the Beta factor from
  -- the resulting product measure.
  calc
    (dirichletPairMeasure θ₁ θ₂).map (fun z : Fin 2 → ℝ ↦ z 0)
        = ((((gammaMeasure θ₁ 1).prod (gammaMeasure θ₂ 1)).map
            (fun p : ℝ × ℝ ↦ ![p.1 / (p.1 + p.2), p.2 / (p.1 + p.2)])).map
            fun z : Fin 2 → ℝ ↦ z 0) := by
          rw [dirichletPairMeasure_eq_map_gammaPairNormalize θ₁ θ₂ hθ₁ hθ₂]
    _ = ((gammaMeasure θ₁ 1).prod (gammaMeasure θ₂ 1)).map
          (fun p : ℝ × ℝ ↦ p.1 / (p.1 + p.2)) := by
          rw [Measure.map_map (measurable_pi_apply 0) hnormalize_meas]
          rfl
    _ = ((((gammaMeasure θ₁ 1).prod (gammaMeasure θ₂ 1)).map ratioSum).map Prod.fst) := by
          rw [hcoord, ← Measure.map_map measurable_fst hratioSum_meas]
    _ = (((betaMeasure θ₁ θ₂).prod (gammaMeasure (θ₁ + θ₂) 1)).map Prod.fst) := by
          rw [map_gammaPair_toRatioSum_eq_prod_beta_gamma θ₁ θ₂ hθ₁ hθ₂]
    _ = betaMeasure θ₁ θ₂ := by
          rw [(measurePreserving_fst
            (μ := betaMeasure θ₁ θ₂) (ν := gammaMeasure (θ₁ + θ₂) 1)).map_eq]

-- Proof sketch: realize the Dirichlet pair by normalized independent Gamma coordinates and
-- identify the first coordinate as the classical Beta-Gamma ratio with parameters `θ₁` and `θ₂`.
/-- Exercise 24.3.1: if the pair `(X, 1 - X)` has the Dirichlet law with positive parameters
`θ₁, θ₂`, interpreted as `dirichletPairMeasure θ₁ θ₂`, then `X` has the Beta law with parameters
`θ₁, θ₂`. -/
theorem hasLaw_beta_of_hasLaw_dirichlet_pair
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {θ₁ θ₂ : ℝ}
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hX : HasLaw (fun ω ↦ ![X ω, 1 - X ω]) (dirichletPairMeasure θ₁ θ₂) μ) :
    HasLaw X (betaMeasure θ₁ θ₂) μ := by
  have hcoord :
      HasLaw (fun z : Fin 2 → ℝ ↦ z 0) (betaMeasure θ₁ θ₂) (dirichletPairMeasure θ₁ θ₂) := by
    -- Proof comment: package the marginal identity of the first Dirichlet coordinate as a
    -- `HasLaw` statement so it can be composed with the given pair-valued law.
    refine
      { aemeasurable := (measurable_pi_apply 0).aemeasurable
        map_eq := map_apply_zero_dirichletPairMeasure_eq_beta θ₁ θ₂ hθ₁ hθ₂ }
  -- Proof comment: compose the coordinate law with the assumed law of `(X, 1 - X)`.
  simpa [Function.comp] using (HasLaw.comp hcoord hX)

end ProbabilityTheory
