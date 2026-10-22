/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_47
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_48

-- Declarations for this item will be appended below by the statement pipeline.

open Complex Filter MeasureTheory ProbabilityTheory
open scoped BigOperators BoundedContinuousFunction ProbabilityTheory Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealRandomVariableArray

/- Lemma 15.49 has three layers in this file.

- `source-facing`: the textbook measures `μₙ(dx) = (1 + x^2)⁻¹ νₙ(dx)` and the two-term expression
  `∫ f_t(x) μₙ(dx) + i t ∫ (1 / x) μₙ(dx)`.
- `core/canonical`: the variance-weighted row laws `A.varianceWeightedRowLaw P n` from
  Lemma 15.48.
- `bridge/view`: rewriting the source expression as an integral against the canonical owner
  measure. -/

/-- The textbook measures `μₙ` from Lemma 15.49, obtained from the variance-weighted row measures
`νₙ` by multiplying with the canonical weight `(1 + x^2)⁻¹`. -/
def cltAuxiliaryMeasure (A : RealRandomVariableArray Ω) (P : Measure Ω) (n : ℕ) : Measure ℝ :=
  (A.varianceWeightedRowMeasure P n).withDensity
    (fun x ↦ ENNReal.ofReal ((1 + x ^ (2 : ℕ))⁻¹))

/-- Helper for Lemma 15.49: the elementary correction identity
`(1 + x^2)⁻¹ / x = 1 / x - x / (1 + x^2)` holds pointwise in `ℂ`. -/
lemma auxiliaryWeight_inv_eq_inv_sub_correction (x : ℝ) :
    ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * (1 / (x : ℂ))) =
      (1 / (x : ℂ)) - (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)) := by
  -- Proof comment: clear the denominator away from `0`; at `x = 0` both sides vanish because
  -- `inv 0 = 0` in Lean.
  by_cases hx : x = 0
  · simp [hx]
  · have hdenR : (1 + x ^ (2 : ℕ) : ℝ) ≠ 0 := by positivity
    have hreal : (1 : ℝ) / (x * (1 + x ^ (2 : ℕ))) =
        1 / x - x / (1 + x ^ (2 : ℕ)) := by
      field_simp [hx, hdenR]
      ring
    simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun r : ℝ ↦ (r : ℂ)) hreal

/-- Helper for Lemma 15.49: the quadratic density `x^2` cancels the singular kernel `1 / x`
down to the identity. -/
private lemma quadraticDensity_mul_inv (x : ℝ) :
    ((((x ^ (2 : ℕ)) : ℝ) : ℂ) * (1 / (x : ℂ))) = (x : ℂ) := by
  -- Proof comment: split into the trivial `x = 0` case and otherwise cancel one factor of `x`
  -- after rewriting the real square as a complex square.
  by_cases hx : x = 0
  · simp [hx]
  · have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    calc
      ((((x ^ (2 : ℕ)) : ℝ) : ℂ) * (1 / (x : ℂ))) = ((x : ℂ) ^ (2 : ℕ)) * (1 / (x : ℂ)) := by
        norm_num
      _ = (x : ℂ) := by
        field_simp [hxC]

/-- Helper for Lemma 15.49: pulling back the weighted correction term along one entry rewrites it
to the cubic correction on `Ω`. -/
private lemma weightedCorrectionPullback_eq_auxiliaryCubicCorrection
    (A : RealRandomVariableArray Ω) (n : ℕ) (i : Fin (A.rowLength n)) :
    (fun ω ↦
      ((((A n i ω) ^ (2 : ℕ) : ℝ) : ℂ) *
        (((A n i ω / (1 + (A n i ω) ^ (2 : ℕ)) : ℝ) : ℂ)))) =
      fun ω ↦ (((A n i ω ^ (3 : ℕ) / (1 + (A n i ω) ^ (2 : ℕ)) : ℝ) : ℂ)) := by
  -- Proof comment: this is the pointwise `x^2 * (x / (1 + x^2)) = x^3 / (1 + x^2)` identity on
  -- the pulled-back entry functions.
  funext ω
  have hreal :
      (A n i ω) ^ (2 : ℕ) * (A n i ω / (1 + (A n i ω) ^ (2 : ℕ))) =
        A n i ω ^ (3 : ℕ) / (1 + (A n i ω) ^ (2 : ℕ)) := by
    ring
  simpa using congrArg (fun r : ℝ ↦ (r : ℂ)) hreal

/-- Helper for Lemma 15.49: the ratio `x^2 / (1 + x^2)` stays below `1`. -/
private lemma auxiliaryQuadraticRatio_le_one (x : ℝ) :
    x ^ (2 : ℕ) / (1 + x ^ (2 : ℕ)) ≤ 1 := by
  -- Proof comment: multiply by the positive denominator `1 + x^2`.
  have hpos : 0 < (1 + x ^ (2 : ℕ) : ℝ) := by positivity
  exact (div_le_iff₀ hpos).2 (by nlinarith [sq_nonneg x])

/-- Helper for Lemma 15.49: the elementary correction `x / (1 + x^2)` is bounded by `1` in
absolute value. -/
private lemma auxiliaryCorrection_abs_le_one (x : ℝ) :
    |x / (1 + x ^ (2 : ℕ))| ≤ 1 := by
  -- Proof comment: rewrite the denominator as a positive real and compare with `|x| ≤ 1 + x^2`.
  have hpos : 0 < (1 + x ^ (2 : ℕ) : ℝ) := by positivity
  rw [abs_div]
  have hden : |(1 + x ^ (2 : ℕ) : ℝ)| = 1 + x ^ (2 : ℕ) := by
    rw [abs_of_nonneg]
    positivity
  rw [hden]
  have hx : |x| ≤ 1 + x ^ (2 : ℕ) := by
    rw [show (x ^ (2 : ℕ) : ℝ) = |x| ^ (2 : ℕ) by rw [sq_abs]]
    nlinarith [sq_nonneg (|x| - (1 / 2 : ℝ))]
  exact (div_le_iff₀ hpos).2 (by simpa using hx)

/-- Helper for Lemma 15.49: the weighted cubic correction is controlled by `|x|`. -/
private lemma norm_auxiliaryCubicCorrection_le_abs (x : ℝ) :
    ‖(((x ^ (3 : ℕ) / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ))‖ ≤ |x| := by
  -- Proof comment: factor out one copy of `x` and bound the remaining quadratic ratio by `1`.
  have hnonneg : 0 ≤ x ^ (2 : ℕ) / (1 + x ^ (2 : ℕ)) := by positivity
  have hratio : x ^ (2 : ℕ) / (1 + x ^ (2 : ℕ)) ≤ 1 :=
    auxiliaryQuadraticRatio_le_one x
  have hsplit :
      (x ^ (3 : ℕ) / (1 + x ^ (2 : ℕ)) : ℝ) =
        x * (x ^ (2 : ℕ) / (1 + x ^ (2 : ℕ))) := by
    ring
  calc
    ‖(((x ^ (3 : ℕ) / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ))‖ =
        |x| * (x ^ (2 : ℕ) / (1 + x ^ (2 : ℕ))) := by
          rw [hsplit, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg]
    _ ≤ |x| * 1 := by gcongr
    _ = |x| := by ring

/-- Helper for Lemma 15.49: the weight `(1 + x^2)⁻¹` rewrites the `μₙ`-integral as an integral
against the owner measure `νₙ`. -/
lemma integral_cltAuxiliaryMeasure_eq_integral_auxiliaryWeight_mul
    (A : RealRandomVariableArray Ω) (P : Measure Ω) (n : ℕ) (g : ℝ →ᵇ ℂ) :
    ∫ x, g x ∂A.cltAuxiliaryMeasure P n =
      ∫ x, ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * g x) ∂A.varianceWeightedRowMeasure P n := by
  -- Proof comment: unfold the textbook measure `μₙ`, rewrite the with-density integral back over
  -- `νₙ`, and then collapse the real scalar action to complex multiplication.
  have hWeightMeas :
      Measurable (fun x : ℝ ↦ ENNReal.ofReal ((1 + x ^ (2 : ℕ))⁻¹)) := by
    fun_prop
  have hWeightFinite :
      ∀ᵐ x ∂A.varianceWeightedRowMeasure P n,
        ENNReal.ofReal ((1 + x ^ (2 : ℕ))⁻¹) < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ by simp
  rw [cltAuxiliaryMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul hWeightMeas hWeightFinite]
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    have htoReal : (ENNReal.ofReal ((1 + x ^ (2 : ℕ))⁻¹)).toReal = (1 + x ^ (2 : ℕ))⁻¹ := by
      simp [inv_nonneg, add_nonneg, sq_nonneg]
    change ((ENNReal.ofReal ((1 + x ^ (2 : ℕ))⁻¹)).toReal : ℝ) • g x =
      ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * g x)
    rw [htoReal, Complex.real_smul]

/-- Helper for Lemma 15.49: the owner correction `x / (1 + x^2)` is integrable against `νₙ`. -/
private lemma integrable_auxiliaryCorrection_varianceWeightedRowMeasure
    (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P] [A.IsCentered P]
    (n : ℕ) :
    Integrable
      (fun x ↦ (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)))
      (A.varianceWeightedRowMeasure P n) := by
  -- Proof comment: prove integrability entrywise on the weighted pushforwards, normalize the
  -- density pullback to the cubic correction, and dominate that correction by `|A n i|`.
  rw [varianceWeightedRowMeasure]
  refine (integrable_finset_sum_measure.2 ?_)
  intro i hi
  let νi : Measure ℝ :=
    (P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))).map (A n i)
  have hCorrectionMeas :
      Measurable (fun x : ℝ ↦ (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ))) := by
    fun_prop
  rw [integrable_map_measure hCorrectionMeas.aestronglyMeasurable
    (A.measurable_entry n i).aemeasurable]
  have hDensityMeas :
      Measurable (fun ω ↦ ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))) := by
    exact ((A.measurable_entry n i).pow_const 2).ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul' hDensityMeas
    (Filter.Eventually.of_forall fun _ ↦ by simp)]
  have hAbsEntry : Integrable (fun ω ↦ |A n i ω|) P := by
    simpa [Real.norm_eq_abs] using
      (RealRandomVariableArray.IsCentered.integrable (A := A) (μ := P) n i).norm
  have hCubicFunMeas :
      Measurable (fun x : ℝ ↦ (((x ^ (3 : ℕ) / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ))) := by
    have hRealCont : Continuous (fun x : ℝ ↦ x ^ (3 : ℕ) / (1 + x ^ (2 : ℕ))) := by
      refine (continuous_id.pow 3).div ?_ fun x ↦ ?_
      · exact continuous_const.add (continuous_id.pow 2)
      · positivity
    exact Complex.continuous_ofReal.measurable.comp hRealCont.measurable
  have hCubicMeas :
      AEStronglyMeasurable
        (fun ω ↦ (((A n i ω ^ (3 : ℕ) / (1 + (A n i ω) ^ (2 : ℕ)) : ℝ) : ℂ))) P := by
    have hCubicAe :
        AEMeasurable
          (fun ω ↦ (((A n i ω ^ (3 : ℕ) / (1 + (A n i ω) ^ (2 : ℕ)) : ℝ) : ℂ))) P :=
      hCubicFunMeas.aemeasurable.comp_aemeasurable (A.measurable_entry n i).aemeasurable
    exact hCubicAe.aestronglyMeasurable
  have hCubicIntegrable :
      Integrable
        (fun ω ↦ (((A n i ω ^ (3 : ℕ) / (1 + (A n i ω) ^ (2 : ℕ)) : ℝ) : ℂ))) P := by
    -- Proof comment: the cubic correction is pointwise bounded by `|A n i|`, so the entry
    -- integrability transfers from centeredness.
    refine hAbsEntry.mono' hCubicMeas ?_
    exact Filter.Eventually.of_forall fun ω ↦
      norm_auxiliaryCubicCorrection_le_abs (A n i ω)
  have hRewrite :
      (fun ω ↦ (ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))).toReal •
          (((A n i ω / (1 + (A n i ω) ^ (2 : ℕ)) : ℝ) : ℂ))) =
        fun ω ↦ (((A n i ω ^ (3 : ℕ) / (1 + (A n i ω) ^ (2 : ℕ)) : ℝ) : ℂ)) := by
    -- Proof comment: rewrite the weighted pullback into the cubic correction normal form before
    -- invoking the domination estimate.
    funext ω
    simpa [smul_eq_mul, ENNReal.toReal_ofReal, sq_nonneg] using
      congrFun (weightedCorrectionPullback_eq_auxiliaryCubicCorrection (A := A) n i) ω
  change Integrable
      (fun x ↦ (ENNReal.ofReal ((A n i x) ^ (2 : ℕ))).toReal •
        (((A n i x / (1 + (A n i x) ^ (2 : ℕ)) : ℝ) : ℂ))) P
  rw [hRewrite]
  exact hCubicIntegrable

/-- Helper for Lemma 15.49: the owner singular kernel `1 / x` is integrable against `νₙ`. -/
private lemma integrable_inv_varianceWeightedRowMeasure
    (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P] [A.IsCentered P]
    (n : ℕ) :
    Integrable (fun x : ℝ ↦ (1 / (x : ℂ))) (A.varianceWeightedRowMeasure P n) := by
  -- Proof comment: as for the correction term, prove the weighted singular integrability one entry
  -- at a time and normalize `x^2 * (1 / x)` down to the entry itself.
  rw [varianceWeightedRowMeasure]
  refine (integrable_finset_sum_measure.2 ?_)
  intro i hi
  have hInvMeas : Measurable (fun x : ℝ ↦ (1 / (x : ℂ))) := by
    fun_prop
  rw [integrable_map_measure hInvMeas.aestronglyMeasurable
    (A.measurable_entry n i).aemeasurable]
  have hDensityMeas :
      Measurable (fun ω ↦ ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))) := by
    exact ((A.measurable_entry n i).pow_const 2).ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul' hDensityMeas
    (Filter.Eventually.of_forall fun _ ↦ by simp)]
  have hEntryIntegrable : Integrable (fun ω ↦ (A n i ω : ℂ)) P := by
    simpa using (RealRandomVariableArray.IsCentered.integrable (A := A) (μ := P) n i).ofReal
  have hRewrite :
      (fun ω ↦ (ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))).toReal • (1 / (A n i ω : ℂ))) =
        fun ω ↦ (A n i ω : ℂ) := by
    -- Proof comment: the density contributes one factor of `A n i`, leaving the centered entry.
    funext ω
    simpa [smul_eq_mul, ENNReal.toReal_ofReal, sq_nonneg] using
      quadraticDensity_mul_inv (A n i ω)
  change Integrable
      (fun x ↦ (ENNReal.ofReal ((A n i x) ^ (2 : ℕ))).toReal • (1 / (A n i x : ℂ))) P
  rw [hRewrite]
  exact hEntryIntegrable

/-- Helper for Lemma 15.49: the owner singular kernel integrates to `0` because the array is
centered. -/
private lemma integral_inv_varianceWeightedRowMeasure_eq_zero
    (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P] [A.IsCentered P]
    (n : ℕ) :
    ∫ x, (1 / (x : ℂ)) ∂A.varianceWeightedRowMeasure P n = 0 := by
  -- Proof comment: expand `νₙ` into its weighted entry measures; each summand rewrites to the
  -- centered expectation of one entry and therefore vanishes.
  rw [varianceWeightedRowMeasure]
  calc
    ∫ x, (1 / (x : ℂ)) ∂∑ i : Fin (A.rowLength n),
        (P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))).map (A n i) =
        ∑ i : Fin (A.rowLength n),
          ∫ x, (1 / (x : ℂ))
            ∂((P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))).map (A n i)) := by
          refine integral_finset_sum_measure ?_
          intro i hi
          have hInvMeas : Measurable (fun x : ℝ ↦ (1 / (x : ℂ))) := by
            fun_prop
          rw [integrable_map_measure hInvMeas.aestronglyMeasurable
            (A.measurable_entry n i).aemeasurable]
          have hDensityMeas :
              Measurable (fun ω ↦ ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))) := by
            exact ((A.measurable_entry n i).pow_const 2).ennreal_ofReal
          rw [integrable_withDensity_iff_integrable_smul' hDensityMeas
            (Filter.Eventually.of_forall fun _ ↦ by simp)]
          have hEntryIntegrable : Integrable (fun ω ↦ (A n i ω : ℂ)) P := by
            simpa using
              (RealRandomVariableArray.IsCentered.integrable (A := A) (μ := P) n i).ofReal
          have hRewrite :
              (fun ω ↦ (ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))).toReal • (1 / (A n i ω : ℂ))) =
                fun ω ↦ (A n i ω : ℂ) := by
            -- Proof comment: the same pointwise normalization used for integrability also gives
            -- the entrywise integral formula.
            funext ω
            simpa [smul_eq_mul, ENNReal.toReal_ofReal, sq_nonneg] using
              quadraticDensity_mul_inv (A n i ω)
          change Integrable
              (fun x ↦ (ENNReal.ofReal ((A n i x) ^ (2 : ℕ))).toReal • (1 / (A n i x : ℂ))) P
          rw [hRewrite]
          exact hEntryIntegrable
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i hi
          calc
            ∫ x, (1 / (x : ℂ))
                ∂((P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))).map (A n i)) =
                ∫ ω, (1 / (A n i ω : ℂ))
                  ∂(P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))) := by
                    have hInvMeas : Measurable (fun x : ℝ ↦ (1 / (x : ℂ))) := by
                      fun_prop
                    rw [integral_map (A.measurable_entry n i).aemeasurable
                      hInvMeas.aestronglyMeasurable]
            _ = ∫ ω, (ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))).toReal • (1 / (A n i ω : ℂ)) ∂P := by
                  have hDensityMeas :
                      Measurable (fun ω ↦ ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))) := by
                    exact ((A.measurable_entry n i).pow_const 2).ennreal_ofReal
                  simpa using
                    (integral_withDensity_eq_integral_toReal_smul hDensityMeas
                      (Filter.Eventually.of_forall fun _ ↦ by simp)
                      (fun ω ↦ (1 / (A n i ω : ℂ))))
            _ = ∫ ω, (A n i ω : ℂ) ∂P := by
                  refine integral_congr_ae ?_
                  exact Filter.Eventually.of_forall fun ω ↦ by
                    simpa [smul_eq_mul, ENNReal.toReal_ofReal, sq_nonneg] using
                      quadraticDensity_mul_inv (A n i ω)
            _ = 0 := by
                  rw [integral_complex_ofReal]
                  simp [RealRandomVariableArray.IsCentered.expectation_eq_zero
                    (A := A) (μ := P) n i]

/-- Helper for Lemma 15.49: the singular term over `μₙ` is the negative bounded correction over
`νₙ`. -/
lemma integral_inv_cltAuxiliaryMeasure_eq_neg_integral_auxiliaryCorrection
    (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P] [A.IsCentered P]
    (n : ℕ) :
    ∫ x, (1 / (x : ℂ)) ∂A.cltAuxiliaryMeasure P n =
      - ∫ x, (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)) ∂A.varianceWeightedRowMeasure P n := by
  -- Proof comment: rewrite the singular `μₙ`-integral back over `νₙ`, split off the correction
  -- term, and then cancel the remaining owner singular integral by centeredness.
  have hInvIntegrable :
      Integrable (fun x : ℝ ↦ (1 / (x : ℂ))) (A.varianceWeightedRowMeasure P n) :=
    integrable_inv_varianceWeightedRowMeasure (A := A) (P := P) n
  have hCorrectionIntegrable :
      Integrable (fun x ↦ (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)))
        (A.varianceWeightedRowMeasure P n) :=
    integrable_auxiliaryCorrection_varianceWeightedRowMeasure (A := A) (P := P) n
  have hWeightMeas :
      Measurable (fun x : ℝ ↦ ENNReal.ofReal ((1 + x ^ (2 : ℕ))⁻¹)) := by
    fun_prop
  have hWeightFinite :
      ∀ᵐ x ∂A.varianceWeightedRowMeasure P n,
        ENNReal.ofReal ((1 + x ^ (2 : ℕ))⁻¹) < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ by simp
  calc
    ∫ x, (1 / (x : ℂ)) ∂A.cltAuxiliaryMeasure P n =
        ∫ x, ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * (1 / (x : ℂ)))
          ∂A.varianceWeightedRowMeasure P n := by
          rw [cltAuxiliaryMeasure]
          rw [integral_withDensity_eq_integral_toReal_smul hWeightMeas hWeightFinite]
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall fun x ↦ by
            have htoReal : (ENNReal.ofReal ((1 + x ^ (2 : ℕ))⁻¹)).toReal = (1 + x ^ (2 : ℕ))⁻¹ := by
              simp [inv_nonneg, add_nonneg, sq_nonneg]
            change ((ENNReal.ofReal ((1 + x ^ (2 : ℕ))⁻¹)).toReal : ℝ) • (1 / (x : ℂ)) =
              ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * (1 / (x : ℂ)))
            rw [htoReal, Complex.real_smul]
    _ = ∫ x, ((1 / (x : ℂ)) - (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)))
          ∂A.varianceWeightedRowMeasure P n := by
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall fun x ↦
            auxiliaryWeight_inv_eq_inv_sub_correction x
    _ =
        ∫ x, (1 / (x : ℂ)) ∂A.varianceWeightedRowMeasure P n -
          ∫ x, (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ))
            ∂A.varianceWeightedRowMeasure P n := by
          rw [integral_sub hInvIntegrable hCorrectionIntegrable]
    _ = - ∫ x, (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ))
          ∂A.varianceWeightedRowMeasure P n := by
          rw [integral_inv_varianceWeightedRowMeasure_eq_zero (A := A) (P := P) n]
          simp

/-- Helper for Lemma 15.49: the weight `(1 + x^2)⁻¹` is continuous on `ℝ`. -/
private lemma continuous_cltAuxiliaryWeight :
    Continuous (fun x : ℝ ↦ ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ))) := by
  -- Proof comment: the denominator `1 + x^2` never vanishes, so inversion preserves continuity.
  refine continuous_ofReal.comp <|
    Continuous.inv₀ (by fun_prop) fun x ↦ ?_
  positivity

/-- Helper for Lemma 15.49: the weight `(1 + x^2)⁻¹` has bounded range. -/
private lemma isBounded_range_cltAuxiliaryWeight :
    Bornology.IsBounded (Set.range fun x : ℝ ↦ ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ))) := by
  -- Proof comment: every value has norm at most `1`, so the whole range sits in a fixed closed
  -- ball.
  refine (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall (0 : ℂ) 1)).subset ?_
  intro z hz
  rcases hz with ⟨x, rfl⟩
  rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  · exact (inv_le_one₀ (by positivity : 0 < (1 + x ^ (2 : ℕ) : ℝ))).2 (by nlinarith [sq_nonneg x])
  · exact inv_nonneg.2 (by positivity : 0 ≤ (1 + x ^ (2 : ℕ) : ℝ))

/-- Helper for Lemma 15.49: the correction `x / (1 + x^2)` is continuous on `ℝ`. -/
private lemma continuous_cltAuxiliaryCorrection :
    Continuous (fun x : ℝ ↦ (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ))) := by
  -- Proof comment: rewrite the correction as `x * (1 + x^2)⁻¹` and combine the continuous factors.
  refine continuous_ofReal.comp ?_
  simpa [div_eq_mul_inv] using
    (continuous_id.mul (Continuous.inv₀ (by fun_prop) fun x ↦ by positivity))

/-- Helper for Lemma 15.49: the correction `x / (1 + x^2)` has bounded range. -/
private lemma isBounded_range_cltAuxiliaryCorrection :
    Bornology.IsBounded (Set.range fun x : ℝ ↦ (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ))) := by
  -- Proof comment: the elementary real bound `|x / (1 + x^2)| ≤ 1` becomes a uniform complex norm
  -- bound on the range.
  refine (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall (0 : ℂ) 1)).subset ?_
  intro z hz
  rcases hz with ⟨x, rfl⟩
  rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero, Complex.norm_real, Real.norm_eq_abs]
  exact auxiliaryCorrection_abs_le_one x

/-- Helper for Lemma 15.49: the owner weight is a bounded continuous function. -/
private def cltAuxiliaryWeightBCF : ℝ →ᵇ ℂ :=
  { toContinuousMap := ⟨fun x ↦ ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ)), continuous_cltAuxiliaryWeight⟩
    map_bounded' := Metric.isBounded_range_iff.1 isBounded_range_cltAuxiliaryWeight }

/-- Helper for Lemma 15.49: coercing the bundled owner weight recovers the explicit formula. -/
@[simp] private lemma coe_cltAuxiliaryWeightBCF :
    (cltAuxiliaryWeightBCF : ℝ → ℂ) = fun x ↦ ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ)) := rfl

/-- Helper for Lemma 15.49: the owner correction is a bounded continuous function. -/
private def cltAuxiliaryCorrectionBCF : ℝ →ᵇ ℂ :=
  { toContinuousMap := ⟨fun x ↦ (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)),
      continuous_cltAuxiliaryCorrection⟩
    map_bounded' := Metric.isBounded_range_iff.1 isBounded_range_cltAuxiliaryCorrection }

/-- Helper for Lemma 15.49: coercing the bundled owner correction recovers the explicit formula. -/
@[simp] private lemma coe_cltAuxiliaryCorrectionBCF :
    (cltAuxiliaryCorrectionBCF : ℝ → ℂ) = fun x ↦ (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)) := rfl

/-- Helper for Lemma 15.49: the final owner-side bridge integrand is a single bounded continuous
test function. -/
private def cltAuxiliaryBridgeBCF (t : ℝ) : ℝ →ᵇ ℂ :=
  cltAuxiliaryWeightBCF * cltAuxiliaryFunctionBCF t +
    BoundedContinuousFunction.const ℝ (-Complex.I * (t : ℂ)) * cltAuxiliaryCorrectionBCF

/-- Helper for Lemma 15.49: the bundled bridge integrand evaluates to the explicit owner formula. -/
@[simp] private lemma cltAuxiliaryBridgeBCF_apply (t x : ℝ) :
    cltAuxiliaryBridgeBCF t x =
      ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * cltAuxiliaryFunction t x) +
        -Complex.I * (t : ℂ) * (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)) := by
  -- Proof comment: unpack the bundled bounded continuous functions and simplify pointwise.
  simp [cltAuxiliaryBridgeBCF, mul_assoc, mul_comm]

/-- Helper for Lemma 15.49: the bridge test function takes the limiting value `-t^2 / 2` at
`0`. -/
private lemma cltAuxiliaryBridgeBCF_apply_zero (t : ℝ) :
    cltAuxiliaryBridgeBCF t 0 = ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
  -- Proof comment: at the origin the correction term vanishes, so only the limiting value of
  -- `cltAuxiliaryFunction t` remains.
  rw [cltAuxiliaryBridgeBCF_apply, cltAuxiliaryFunction_apply_zero]
  simp

/-- Helper for Lemma 15.49: after pulling the weighted `f_t` term back through one entry law, the
with-density scalar becomes the quadratic ratio `x^2 / (1 + x^2)`. -/
private lemma weightedAuxiliaryFunctionPullback_eq_quadraticRatio_mul
    (A : RealRandomVariableArray Ω) (n : ℕ) (i : Fin (A.rowLength n)) (t : ℝ) :
    (fun ω ↦
      (ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))).toReal •
        ((((1 + (A n i ω) ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * cltAuxiliaryFunction t (A n i ω))) =
      fun ω ↦
        ((((A n i ω) ^ (2 : ℕ) / (1 + (A n i ω) ^ (2 : ℕ)) : ℝ) : ℂ) *
          cltAuxiliaryFunction t (A n i ω)) := by
  -- Proof comment: collapse the density scalar and the textbook weight into the single quadratic
  -- ratio normal form before any integrability argument.
  funext ω
  simp [ENNReal.toReal_ofReal, sq_nonneg, div_eq_mul_inv, mul_left_comm, mul_comm]

/-- Helper for Lemma 15.49: the pulled-back quadratic-ratio-weighted auxiliary function is
integrable on the source probability space. -/
private lemma integrable_quadraticRatio_mul_cltAuxiliaryFunction_entry
    (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (i : Fin (A.rowLength n)) (t : ℝ) :
    Integrable
      (fun ω ↦
        ((((A n i ω) ^ (2 : ℕ) / (1 + (A n i ω) ^ (2 : ℕ)) : ℝ) : ℂ) *
          cltAuxiliaryFunction t (A n i ω))) P := by
  have hFtMap :
      Integrable (fun x : ℝ ↦ cltAuxiliaryFunction t x) (P.map (A n i)) := by
    -- Proof comment: the bounded continuous function from Lemma 15.47 is integrable against every
    -- probability measure, hence in particular against the entry law.
    simpa using
      (BoundedContinuousFunction.integrable (μ := P.map (A n i)) (cltAuxiliaryFunctionBCF t))
  have hFtMeas : Measurable (fun x : ℝ ↦ cltAuxiliaryFunction t x) := by
    simpa using (continuous_cltAuxiliaryFunction t).measurable
  have hFtPullback :
      Integrable (fun ω ↦ cltAuxiliaryFunction t (A n i ω)) P := by
    -- Proof comment: transport the bounded auxiliary function back from the entry law to the
    -- source space through `A n i`.
    rw [integrable_map_measure hFtMeas.aestronglyMeasurable
      (A.measurable_entry n i).aemeasurable] at hFtMap
    simpa using hFtMap
  have hRatioMeas :
      Measurable
        (fun ω ↦ ((((A n i ω) ^ (2 : ℕ) / (1 + (A n i ω) ^ (2 : ℕ)) : ℝ) : ℂ))) := by
    have hSqMeas : Measurable (fun ω ↦ (A n i ω) ^ (2 : ℕ)) :=
      (A.measurable_entry n i).pow_const 2
    have hInvMeas : Measurable (fun ω ↦ ((1 + (A n i ω) ^ (2 : ℕ) : ℝ)⁻¹)) :=
      (measurable_const.add hSqMeas).inv
    have hRatioRealMeas :
        Measurable (fun ω ↦ (A n i ω) ^ (2 : ℕ) / (1 + (A n i ω) ^ (2 : ℕ) : ℝ)) := by
      simpa [div_eq_mul_inv] using hSqMeas.mul hInvMeas
    exact Complex.continuous_ofReal.measurable.comp hRatioRealMeas
  have hFtPullbackMeas : Measurable (fun ω ↦ cltAuxiliaryFunction t (A n i ω)) :=
    hFtMeas.comp (A.measurable_entry n i)
  have hWeightedMeas :
      AEStronglyMeasurable
        (fun ω ↦
          ((((A n i ω) ^ (2 : ℕ) / (1 + (A n i ω) ^ (2 : ℕ)) : ℝ) : ℂ) *
            cltAuxiliaryFunction t (A n i ω))) P :=
    (hRatioMeas.mul hFtPullbackMeas).aemeasurable.aestronglyMeasurable
  refine hFtPullback.norm.mono' hWeightedMeas ?_
  exact Filter.Eventually.of_forall fun ω ↦ by
    -- Proof comment: the quadratic ratio stays in `[0,1]`, so multiplying by it cannot increase
    -- the norm of the pulled-back bounded test function.
    have hratio_nonneg : 0 ≤ (A n i ω) ^ (2 : ℕ) / (1 + (A n i ω) ^ (2 : ℕ)) := by
      positivity
    have hratio_le :
        (A n i ω) ^ (2 : ℕ) / (1 + (A n i ω) ^ (2 : ℕ)) ≤ 1 :=
      auxiliaryQuadraticRatio_le_one (A n i ω)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hratio_nonneg]
    nlinarith [norm_nonneg (cltAuxiliaryFunction t (A n i ω)), hratio_le]

/-- Helper for Lemma 15.49: the owner-side weighted auxiliary term is integrable against the
variance-weighted row measure. -/
private lemma integrable_auxiliaryWeight_mul_cltAuxiliaryFunction_varianceWeightedRowMeasure
    (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (t : ℝ) :
    Integrable
      (fun x ↦ ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * cltAuxiliaryFunction t x))
      (A.varianceWeightedRowMeasure P n) := by
  -- Proof comment: expand the owner measure into its weighted entry laws and reduce each summand
  -- to the pullback integrability result above.
  rw [varianceWeightedRowMeasure]
  refine (integrable_finset_sum_measure.2 ?_)
  intro i hi
  have hWeightFtMeas :
      Measurable
        (fun x : ℝ ↦ ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * cltAuxiliaryFunction t x)) := by
    exact continuous_cltAuxiliaryWeight.measurable.mul
      (by simpa using (continuous_cltAuxiliaryFunction t).measurable)
  rw [integrable_map_measure hWeightFtMeas.aestronglyMeasurable
    (A.measurable_entry n i).aemeasurable]
  have hDensityMeas :
      Measurable (fun ω ↦ ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))) := by
    exact ((A.measurable_entry n i).pow_const 2).ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul' hDensityMeas
    (Filter.Eventually.of_forall fun _ ↦ by simp)]
  change Integrable
    (fun ω ↦
      (ENNReal.ofReal ((A n i ω) ^ (2 : ℕ))).toReal •
        ((((1 + (A n i ω) ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * cltAuxiliaryFunction t (A n i ω))) P
  rw [weightedAuxiliaryFunctionPullback_eq_quadraticRatio_mul (A := A) n i t]
  exact integrable_quadraticRatio_mul_cltAuxiliaryFunction_entry (A := A) (P := P) n i t

-- Proof sketch: rewrite the `f_t`-integral against `μₙ` directly using
-- `μₙ = (1 + x^2)⁻¹ νₙ`. For the singular term, first write
-- `1 / (x * (1 + x^2)) = 1 / x - x / (1 + x^2)` and then use centeredness of the array to cancel
-- the `∫ (1 / x) νₙ(dx)` contribution, leaving the bounded correction
-- `-x / (1 + x^2)` against the owner measure `νₙ`.
/-- Lemma 15.49: the textbook two-term expression is canonically a single integral against the
variance-weighted owner measure `νₙ`. -/
theorem cltAuxiliaryMeasure_expression_eq_integral_varianceWeightedRowMeasure
    (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P] [A.IsCentered P]
    (n : ℕ) (t : ℝ) :
    (∫ x, cltAuxiliaryFunction t x ∂A.cltAuxiliaryMeasure P n) +
        Complex.I * (t : ℂ) * (∫ x, (1 / (x : ℂ)) ∂A.cltAuxiliaryMeasure P n) =
      ∫ x,
        ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * cltAuxiliaryFunction t x +
          -Complex.I * (t : ℂ) * (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)))
        ∂A.varianceWeightedRowMeasure P n := by
  -- Route correction: keep the with-density normalization out of the theorem body and package the
  -- weighted `f_t` integrability as a dedicated owner-side bridge lemma first.
  have hWeightInt :
      Integrable
        (fun x ↦ ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * cltAuxiliaryFunction t x))
        (A.varianceWeightedRowMeasure P n) :=
    integrable_auxiliaryWeight_mul_cltAuxiliaryFunction_varianceWeightedRowMeasure
      (A := A) (P := P) n t
  have hCorrectionInt :
      Integrable
        (fun x ↦ -Complex.I * (t : ℂ) * (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)))
        (A.varianceWeightedRowMeasure P n) :=
    (integrable_auxiliaryCorrection_varianceWeightedRowMeasure (A := A) (P := P) n).const_mul
      (-Complex.I * (t : ℂ))
  have hFirst :
      ∫ x, cltAuxiliaryFunction t x ∂A.cltAuxiliaryMeasure P n =
        ∫ x, ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * cltAuxiliaryFunction t x)
          ∂A.varianceWeightedRowMeasure P n := by
    -- Proof comment: the bounded continuous `f_t` term rewrites directly through the owner
    -- measure bridge from the previous helper theorem.
    simpa using
      (integral_cltAuxiliaryMeasure_eq_integral_auxiliaryWeight_mul
        (A := A) (P := P) n (cltAuxiliaryFunctionBCF t))
  have hSecond :
      ∫ x, (1 / (x : ℂ)) ∂A.cltAuxiliaryMeasure P n =
        - ∫ x, (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ))
          ∂A.varianceWeightedRowMeasure P n := by
    -- Proof comment: the singular kernel was already normalized to the bounded correction term.
    simpa using
      (integral_inv_cltAuxiliaryMeasure_eq_neg_integral_auxiliaryCorrection
        (A := A) (P := P) n)
  have hConstMul :
      (-Complex.I * (t : ℂ)) *
          (∫ x, (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ))
            ∂A.varianceWeightedRowMeasure P n) =
        ∫ x, -Complex.I * (t : ℂ) * (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ))
          ∂A.varianceWeightedRowMeasure P n := by
    -- Proof comment: move the constant complex prefactor inside the correction integral once.
    simpa using
      (integral_const_mul (-Complex.I * (t : ℂ))
        (fun x : ℝ ↦ (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)))
        (μ := A.varianceWeightedRowMeasure P n)).symm
  calc
    (∫ x, cltAuxiliaryFunction t x ∂A.cltAuxiliaryMeasure P n) +
        Complex.I * (t : ℂ) * (∫ x, (1 / (x : ℂ)) ∂A.cltAuxiliaryMeasure P n) =
        (∫ x, ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * cltAuxiliaryFunction t x)
          ∂A.varianceWeightedRowMeasure P n) +
          (-Complex.I * (t : ℂ)) *
            (∫ x, (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ))
              ∂A.varianceWeightedRowMeasure P n) := by
          -- Proof comment: rewrite the two textbook source integrals separately into owner-measure
          -- form before combining them.
          rw [hFirst, hSecond]
          ring
    _ =
        (∫ x, ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * cltAuxiliaryFunction t x)
          ∂A.varianceWeightedRowMeasure P n) +
          ∫ x, -Complex.I * (t : ℂ) * (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ))
            ∂A.varianceWeightedRowMeasure P n := by
          -- Proof comment: replace the scalar multiple of the correction integral by the integral
          -- of the scaled correction kernel.
          rw [hConstMul]
    _ = ∫ x,
          ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * cltAuxiliaryFunction t x +
            -Complex.I * (t : ℂ) * (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)))
          ∂A.varianceWeightedRowMeasure P n := by
          -- Proof comment: once both owner-side terms are integrable, the target is exactly their
          -- sum under a single integral.
          rw [← integral_add hWeightInt hCorrectionInt]

-- Proof sketch: use the preceding centered bridge rewrite, where the Lindeberg hypothesis supplies
-- the needed centeredness instance, and combine it with weak convergence of `νₙ` to `δ₀` from
-- Lemma 15.48, applied to the bounded continuous bridge integrand on the right-hand side. Then
-- evaluate the limiting Dirac integral at `0`.
/-- Consequence of Lemma 15.49: for an independent normed real random-variable array satisfying the
Lindeberg condition, the textbook expression
`∫ f_t(x) μₙ(dx) + i t ∫ (1 / x) μₙ(dx)` converges to `-t^2 / 2`. -/
theorem tendsto_cltAuxiliaryMeasure_expression
    (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    [A.IsIndependent P] [A.IsNormed P]
    (h_lindeberg : A.SatisfiesLindebergCondition P) (t : ℝ) :
    Tendsto
      (fun n ↦
        (∫ x, cltAuxiliaryFunction t x ∂A.cltAuxiliaryMeasure P n) +
          Complex.I * (t : ℂ) * (∫ x, (1 / (x : ℂ)) ∂A.cltAuxiliaryMeasure P n))
      atTop
      (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
  -- Proof comment: first rewrite the textbook expression as one integral of the bounded
  -- continuous bridge test function, then apply weak convergence of the variance-weighted row laws.
  letI : A.IsCentered P := h_lindeberg.toIsCentered
  have hWeighted :
      Tendsto (fun n ↦ A.varianceWeightedRowLaw P n) atTop (𝓝 (diracProba (0 : ℝ))) :=
    A.varianceWeightedRowLaw_tendsto_diracProba_zero_of_satisfiesLindebergCondition P h_lindeberg
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at hWeighted
  have hBridgeEq :
      (fun n ↦
        (∫ x, cltAuxiliaryFunction t x ∂A.cltAuxiliaryMeasure P n) +
          Complex.I * (t : ℂ) * (∫ x, (1 / (x : ℂ)) ∂A.cltAuxiliaryMeasure P n)) =
        fun n ↦ ∫ x, cltAuxiliaryBridgeBCF t x ∂(A.varianceWeightedRowLaw P n : Measure ℝ) := by
    funext n
    calc
      (∫ x, cltAuxiliaryFunction t x ∂A.cltAuxiliaryMeasure P n) +
          Complex.I * (t : ℂ) * (∫ x, (1 / (x : ℂ)) ∂A.cltAuxiliaryMeasure P n) =
          ∫ x,
            ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * cltAuxiliaryFunction t x +
              -Complex.I * (t : ℂ) * (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)))
            ∂A.varianceWeightedRowMeasure P n := by
              exact cltAuxiliaryMeasure_expression_eq_integral_varianceWeightedRowMeasure
                (A := A) (P := P) n t
      _ = ∫ x, cltAuxiliaryBridgeBCF t x ∂A.varianceWeightedRowMeasure P n := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun x ↦ by
              rw [cltAuxiliaryBridgeBCF_apply]
      _ = ∫ x, cltAuxiliaryBridgeBCF t x ∂(A.varianceWeightedRowLaw P n : Measure ℝ) := by
            rw [A.varianceWeightedRowLaw_toMeasure P n]
  have hBridgeIntegral :
      Tendsto
        (fun n ↦ ∫ x, cltAuxiliaryBridgeBCF t x ∂(A.varianceWeightedRowLaw P n : Measure ℝ))
        atTop
        (𝓝
          (∫ x, cltAuxiliaryBridgeBCF t x
            ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ))) :=
    hWeighted (cltAuxiliaryBridgeBCF t)
  have hDirac :
      (∫ x, cltAuxiliaryBridgeBCF t x
        ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) =
        ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
    rw [show (((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) = Measure.dirac (0 : ℝ)
      by rfl]
    rw [integral_dirac]
    simpa using cltAuxiliaryBridgeBCF_apply_zero t
  rw [hBridgeEq]
  rw [show ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) =
      (∫ x, cltAuxiliaryBridgeBCF t x
        ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) by
      simpa using hDirac.symm]
  exact hBridgeIntegral

-- Proof sketch: apply weak convergence of `A.varianceWeightedRowLaw P n` to `diracProba 0`
-- from Lemma 15.48 via the canonical bounded continuous test function `cltAuxiliaryFunctionBCF t`
-- from Lemma 15.47, then evaluate the limiting Dirac integral at `0`.
/-- Bridge/view consequence: for an independent normed array satisfying the Lindeberg condition,
the canonical variance-weighted row laws `νₙ` integrate the bounded continuous test function from
Lemma 15.47 to the same limit `-t^2 / 2`. -/
theorem tendsto_integral_cltAuxiliaryFunctionBCF_varianceWeightedRowLaw
    (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    [A.IsIndependent P] [A.IsNormed P]
    (h_lindeberg : A.SatisfiesLindebergCondition P) (t : ℝ) :
    Tendsto
      (fun n ↦ ∫ x, cltAuxiliaryFunctionBCF t x ∂(A.varianceWeightedRowLaw P n : Measure ℝ))
      atTop
      (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
  letI : A.IsCentered P := h_lindeberg.toIsCentered
  have h_tendsto :
      Tendsto (fun n ↦ A.varianceWeightedRowLaw P n) atTop (𝓝 (diracProba (0 : ℝ))) :=
    A.varianceWeightedRowLaw_tendsto_diracProba_zero_of_satisfiesLindebergCondition P h_lindeberg
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at h_tendsto
  have h_integral :
      Tendsto
        (fun n ↦ ∫ x, cltAuxiliaryFunctionBCF t x ∂(A.varianceWeightedRowLaw P n : Measure ℝ))
        atTop
        (𝓝
          (∫ x, cltAuxiliaryFunctionBCF t x
            ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ))) :=
    h_tendsto (cltAuxiliaryFunctionBCF t)
  have h_dirac :
      (∫ x, cltAuxiliaryFunctionBCF t x
        ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) =
        ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
    rw [show (((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) = Measure.dirac (0 : ℝ)
      by rfl]
    rw [integral_dirac]
    simp [cltAuxiliaryFunction_apply_zero]
  rw [show ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) =
      (∫ x, cltAuxiliaryFunctionBCF t x
        ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) by
      simpa using h_dirac.symm]
  exact h_integral

end RealRandomVariableArray
