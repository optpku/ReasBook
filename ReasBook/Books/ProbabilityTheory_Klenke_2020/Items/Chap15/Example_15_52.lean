/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The symmetric Pareto-type density obtained by symmetrizing the canonical Pareto density
`paretoPDFReal 1 (1 / α)` along `x ↦ |x|`. -/
def symmetricParetoDensityReal (α x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * paretoPDFReal 1 (1 / α) |x|

/-- The symmetric Pareto density is the textbook power-law density
`x ↦ (2 α)⁻¹ |x|^(-1 - 1 / α) 1_{|x| ≥ 1}(x)`. -/
theorem symmetricParetoDensityReal_eq (α x : ℝ) :
    symmetricParetoDensityReal α x =
      if 1 ≤ |x| then (1 / (2 * α)) * |x| ^ (-1 - 1 / α) else 0 := by
  -- Rewrite the symmetrized density through the Pareto density at `|x|`.
  by_cases hx : 1 ≤ |x|
  · rw [symmetricParetoDensityReal, paretoPDFReal, if_pos hx, if_pos hx]
    -- Only a scalar simplification remains.
    simp [Real.one_rpow]
    ring_nf
  · rw [symmetricParetoDensityReal, paretoPDFReal, if_neg hx, if_neg hx]
    simp

/-- Helper for Example 15.52: the `ENNReal` density of the symmetric law splits into the
canonical Pareto density and its reflection. -/
lemma symmetricParetoDensityReal_toENNReal_eq_half_add_reflected (α x : ℝ) :
    ENNReal.ofReal (symmetricParetoDensityReal α x) =
      (1 / 2 : ENNReal) * paretoPDF 1 (1 / α) x +
        (1 / 2 : ENNReal) * paretoPDF 1 (1 / α) (-x) := by
  by_cases habs : 1 ≤ |x|
  · by_cases hx : 0 ≤ x
    · have hx1 : 1 ≤ x := by rwa [abs_of_nonneg hx] at habs
      have hneglt : -x < 1 := by linarith
      -- On the positive half-line only the non-reflected Pareto term survives.
      rw [symmetricParetoDensityReal, abs_of_nonneg hx, paretoPDF_of_le hx1, paretoPDF_of_lt hneglt]
      simp [paretoPDFReal, hx1, ENNReal.ofReal_mul, Real.one_rpow]
    · have hxlt : x < 0 := lt_of_not_ge hx
      have hneg1 : 1 ≤ -x := by simpa [abs_of_neg hxlt] using habs
      have hxlt1 : x < 1 := by linarith
      -- On the negative half-line only the reflected Pareto term survives.
      rw [symmetricParetoDensityReal, abs_of_neg hxlt, paretoPDF_of_lt hxlt1, paretoPDF_of_le hneg1]
      simp [paretoPDFReal, hneg1, ENNReal.ofReal_mul, Real.one_rpow]
  · have habs_lt : |x| < 1 := lt_of_not_ge habs
    have hxlt : x < 1 := lt_of_le_of_lt (le_abs_self x) habs_lt
    have hneglt : -x < 1 := lt_of_le_of_lt (neg_le_abs x) habs_lt
    -- Away from `|x| ≥ 1`, both Pareto terms vanish.
    rw [symmetricParetoDensityReal, paretoPDF_of_lt hxlt, paretoPDF_of_lt hneglt]
    simp [paretoPDFReal, habs, ENNReal.ofReal_zero]

/-- Helper for Example 15.52: reflecting a measurable density across `x ↦ -x` rewrites the
restricted Lebesgue `lintegral` on a measurable set. -/
lemma lintegral_preimage_neg_eq (f : ℝ → ℝ≥0∞) (hf : Measurable f) {s : Set ℝ}
    (hs : MeasurableSet s) :
    ∫⁻ x in (fun x : ℝ ↦ -x) ⁻¹' s, f x ∂volume = ∫⁻ x in s, f (-x) ∂volume := by
  have hneg_meas : Measurable (fun x : ℝ ↦ -x) := by fun_prop
  have hmap :
      ∫⁻ y in s, f (-y) ∂volume = ∫⁻ x in (fun x : ℝ ↦ -x) ⁻¹' s, f x ∂volume := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    simpa [Function.comp] using
      (setLIntegral_map
        (μ := (volume : Measure ℝ))
        (g := fun x : ℝ ↦ -x)
        (f := fun y : ℝ ↦ f (-y))
        hs
        (hf.comp hneg_meas)
        hneg_meas)
  exact hmap.symm

/-- The symmetric Pareto-type law on `ℝ` with Lebesgue density
`symmetricParetoDensityReal α`. -/
def symmetricParetoMeasure (α : ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (symmetricParetoDensityReal α x))

/-- The density-defined symmetric Pareto law agrees with the symmetrized canonical Pareto law
obtained by averaging `paretoMeasure 1 (1 / α)` and its reflection. -/
theorem symmetricParetoMeasure_eq_symmetrized_paretoMeasure (α : ℝ) :
    symmetricParetoMeasure α =
      (1 / 2 : ENNReal) • paretoMeasure 1 (1 / α) +
        (1 / 2 : ENNReal) • (paretoMeasure 1 (1 / α)).map (fun x ↦ -x) := by
  have hpareto_meas : Measurable (paretoPDF 1 (1 / α)) := by
    simpa [paretoPDF] using (measurable_paretoPDFReal 1 (1 / α)).ennreal_ofReal
  have hpareto_reflect_meas : Measurable (fun x : ℝ ↦ paretoPDF 1 (1 / α) (-x)) :=
    hpareto_meas.comp (by fun_prop)
  have hhalf_pareto_reflect_meas :
      Measurable (fun x : ℝ ↦ (1 / 2 : ENNReal) * paretoPDF 1 (1 / α) (-x)) := by
    fun_prop
  ext s hs
  -- Rewrite all measures through their density formulas on the same measurable set.
  rw [symmetricParetoMeasure, withDensity_apply _ hs]
  rw [show (fun x ↦ ENNReal.ofReal (symmetricParetoDensityReal α x)) =
      fun x ↦ (1 / 2 : ENNReal) * paretoPDF 1 (1 / α) x
        + (1 / 2 : ENNReal) * paretoPDF 1 (1 / α) (-x) by
      funext x
      exact symmetricParetoDensityReal_toENNReal_eq_half_add_reflected α x]
  have hadd :
      ∫⁻ x in s, (1 / 2 : ENNReal) * paretoPDF 1 (1 / α) x +
          (1 / 2 : ENNReal) * paretoPDF 1 (1 / α) (-x) ∂volume =
        ∫⁻ x in s, (1 / 2 : ENNReal) * paretoPDF 1 (1 / α) x ∂volume +
          ∫⁻ x in s, (1 / 2 : ENNReal) * paretoPDF 1 (1 / α) (-x) ∂volume := by
    simpa using
      (lintegral_add_right
        (μ := volume.restrict s)
        (f := fun x : ℝ ↦ (1 / 2 : ENNReal) * paretoPDF 1 (1 / α) x)
        (g := fun x : ℝ ↦ (1 / 2 : ENNReal) * paretoPDF 1 (1 / α) (-x))
        hhalf_pareto_reflect_meas)
  have hbase_apply :
      ((1 / 2 : ENNReal) • paretoMeasure 1 (1 / α)) s =
        (1 / 2 : ENNReal) * ∫⁻ x in s, paretoPDF 1 (1 / α) x ∂volume := by
    rw [Measure.coe_smul, Pi.smul_apply, smul_eq_mul, paretoMeasure, withDensity_apply _ hs]
  have hmap_apply :
      ((1 / 2 : ENNReal) • (paretoMeasure 1 (1 / α)).map (fun x : ℝ ↦ -x)) s =
        (1 / 2 : ENNReal) * ∫⁻ x in s, paretoPDF 1 (1 / α) (-x) ∂volume := by
    rw [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [Measure.map_apply (by fun_prop) hs, paretoMeasure]
    rw [withDensity_apply _ ((by fun_prop : Measurable (fun x : ℝ ↦ -x)) hs)]
    rw [lintegral_preimage_neg_eq (f := paretoPDF 1 (1 / α)) hpareto_meas hs]
  calc
    ∫⁻ x in s, (1 / 2 : ENNReal) * paretoPDF 1 (1 / α) x +
        (1 / 2 : ENNReal) * paretoPDF 1 (1 / α) (-x) ∂volume
      = (1 / 2 : ENNReal) * ∫⁻ x in s, paretoPDF 1 (1 / α) x ∂volume +
          (1 / 2 : ENNReal) * ∫⁻ x in s, paretoPDF 1 (1 / α) (-x) ∂volume := by
            rw [hadd]
            rw [lintegral_const_mul _ hpareto_meas]
            rw [lintegral_const_mul _ hpareto_reflect_meas]
    _ = ((1 / 2 : ENNReal) • paretoMeasure 1 (1 / α)) s +
          ((1 / 2 : ENNReal) • (paretoMeasure 1 (1 / α)).map (fun x : ℝ ↦ -x)) s := by
            rw [hbase_apply, hmap_apply]
    _ = ((1 / 2 : ENNReal) • paretoMeasure 1 (1 / α) +
          (1 / 2 : ENNReal) • (paretoMeasure 1 (1 / α)).map (fun x : ℝ ↦ -x)) s := by
            rw [Measure.add_apply]

-- Proof sketch: rewrite `symmetricParetoMeasure α` using
-- `symmetricParetoMeasure_eq_symmetrized_paretoMeasure`, then combine
-- `isProbabilityMeasure_paretoMeasure 1 (1 / α)` with the preserved total mass under reflection.
/-- For `α > 0`, the symmetric Pareto law has total mass `1`. -/
theorem isProbabilityMeasure_symmetricParetoMeasure (α : ℝ) (hα0 : 0 < α) :
    IsProbabilityMeasure (symmetricParetoMeasure α) where
  measure_univ := by
    letI : IsProbabilityMeasure (paretoMeasure 1 (1 / α)) :=
      isProbabilityMeasure_paretoMeasure zero_lt_one (one_div_pos.mpr hα0)
    have hpareto_univ : (paretoMeasure 1 (1 / α)) Set.univ = 1 := by
      exact IsProbabilityMeasure.measure_univ
    have hmap_univ :
        (paretoMeasure 1 (1 / α)).map (fun x : ℝ ↦ -x) Set.univ = 1 := by
      rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
      exact hpareto_univ
    -- The symmetrized law is the average of two probability measures.
    calc
      symmetricParetoMeasure α Set.univ
          = ((1 / 2 : ENNReal) • paretoMeasure 1 (1 / α) +
              (1 / 2 : ENNReal) • (paretoMeasure 1 (1 / α)).map (fun x : ℝ ↦ -x)) Set.univ := by
                rw [symmetricParetoMeasure_eq_symmetrized_paretoMeasure α]
      _ = (1 / 2 : ENNReal) * (paretoMeasure 1 (1 / α)) Set.univ +
            (1 / 2 : ENNReal) * ((paretoMeasure 1 (1 / α)).map (fun x : ℝ ↦ -x)) Set.univ := by
              simp [Measure.add_apply, smul_eq_mul]
      _ = (1 / 2 : ENNReal) * 1 + (1 / 2 : ENNReal) * 1 := by rw [hpareto_univ, hmap_univ]
      _ = 1 := by
            simpa using ENNReal.inv_two_add_inv_two

/-- Helper for Example 15.52: the second moment of `paretoMeasure 1 (1 / α)` is
`1 / (1 - 2 * α)` when `0 < α < 1 / 2`. -/
lemma integral_sq_paretoMeasure_one_invAlpha (α : ℝ) (hα0 : 0 < α) (hα_half : α < 1 / 2) :
    ∫ x, x ^ 2 ∂paretoMeasure 1 (1 / α) = 1 / (1 - 2 * α) := by
  have hshape_pos : 0 < 1 / α := one_div_pos.mpr hα0
  have hExp : 1 - 1 / α < -1 := by
    have htwo : (2 : ℝ) < 1 / α := by
      rw [_root_.lt_div_iff₀ hα0]
      linarith
    linarith
  have hpareto_meas : Measurable (paretoPDF 1 (1 / α)) := by
    simpa [paretoPDF] using (measurable_paretoPDFReal 1 (1 / α)).ennreal_ofReal
  have hIntegrand :
      (fun x : ℝ ↦ (paretoPDF 1 (1 / α) x).toReal • x ^ 2) =
        Set.indicator (Set.Ici (1 : ℝ)) (fun x : ℝ ↦ (1 / α) * x ^ (1 - 1 / α)) := by
    funext x
    by_cases hx : 1 ≤ x
    · have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
      have hxmem : x ∈ Set.Ici (1 : ℝ) := hx
      rw [paretoPDF_of_le hx, ENNReal.toReal_ofReal]
      · rw [smul_eq_mul, Set.indicator_of_mem hxmem]
        have hxpow : x ^ (2 : ℕ) = x ^ (2 : ℝ) := by
          exact (Real.rpow_natCast x 2).symm
        have hrpow : x ^ (-(1 / α + 1)) * x ^ (2 : ℝ) = x ^ (1 - 1 / α) := by
          rw [← Real.rpow_add hx0]
          congr 1
          ring
        rw [hxpow]
        calc
          ((1 / α) * 1 ^ (1 / α) * x ^ (-(1 / α + 1))) * x ^ (2 : ℝ)
              = (1 / α) * (x ^ (-(1 / α + 1)) * x ^ (2 : ℝ)) := by
                  simp [Real.one_rpow, mul_left_comm, mul_comm]
          _ = (1 / α) * x ^ (1 - 1 / α) := by rw [hrpow]
      · positivity
    · have hxmem : x ∉ Set.Ici (1 : ℝ) := hx
      rw [paretoPDF_of_lt (lt_of_not_ge hx), ENNReal.toReal_zero, zero_smul,
        Set.indicator_of_notMem hxmem]
  -- Convert the density integral to a scalar multiple of a power integral on `(1, ∞)`.
  rw [paretoMeasure,
    integral_withDensity_eq_integral_toReal_smul
      hpareto_meas
      (by
        filter_upwards with x
        simp [paretoPDF]),
    hIntegrand, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_Ioi_rpow_of_lt hExp zero_lt_one]
  have hden : 2 - 1 / α ≠ 0 := by
    linarith
  field_simp [hα0.ne', hden]
  have hrewrite : -(α - 1 + α) = 1 - α * 2 := by ring
  rw [Real.one_rpow, one_div, neg_inv]
  simpa using congrArg Inv.inv hrewrite

/-- Helper for Example 15.52: the symmetric Pareto law has the same second moment as the base
Pareto law because `x ↦ x ^ 2` is even. -/
lemma integral_sq_symmetricParetoMeasure (α : ℝ) (hα0 : 0 < α) (hα_half : α < 1 / 2) :
    ∫ x, x ^ 2 ∂symmetricParetoMeasure α = 1 / (1 - 2 * α) := by
  let μ : Measure ℝ := paretoMeasure 1 (1 / α)
  have hsq :
      ∫ x, x ^ 2 ∂μ = 1 / (1 - 2 * α) :=
    integral_sq_paretoMeasure_one_invAlpha α hα0 hα_half
  have hsq_int : Integrable (fun x : ℝ ↦ x ^ 2) μ := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hsq]
    have hpos : 0 < 1 / (1 - 2 * α) := by
      have : 0 < 1 - 2 * α := by linarith
      positivity
    exact ne_of_gt hpos
  have hsq_map_int : Integrable (fun x : ℝ ↦ x ^ 2) (μ.map (fun x ↦ -x)) := by
    have hsq_comp : Integrable ((fun x : ℝ ↦ x ^ 2) ∘ fun x : ℝ ↦ -x) μ := by
      simpa [Function.comp_def, sq] using hsq_int
    exact (integrable_map_equiv (μ := μ) (MeasurableEquiv.neg ℝ) (fun x : ℝ ↦ x ^ 2)).2 hsq_comp
  have hsq_map :
      ∫ x, x ^ 2 ∂μ.map (fun x : ℝ ↦ -x) = ∫ x, x ^ 2 ∂μ := by
    have hmap_raw :
        ∫ x, x ^ 2 ∂Measure.map Neg.neg μ = ∫ x, (-x) ^ 2 ∂μ := by
      exact integral_map_equiv (μ := μ) (MeasurableEquiv.neg ℝ) (fun x : ℝ ↦ x ^ 2)
    calc
      ∫ x, x ^ 2 ∂μ.map (fun x : ℝ ↦ -x) = ∫ x, x ^ 2 ∂Measure.map Neg.neg μ := by rfl
      _ = ∫ x, (-x) ^ 2 ∂μ := hmap_raw
      _ = ∫ x, x ^ 2 ∂μ := by simp [sq]
  -- Rewrite the symmetric law as the average of the base law and its reflection.
  calc
    ∫ x, x ^ 2 ∂symmetricParetoMeasure α
        = ∫ x, x ^ 2 ∂((1 / 2 : ℝ≥0∞) • μ + (1 / 2 : ℝ≥0∞) • μ.map (fun x : ℝ ↦ -x)) := by
            rw [symmetricParetoMeasure_eq_symmetrized_paretoMeasure α]
    _ =
        ∫ x, x ^ 2 ∂((1 / 2 : ℝ≥0∞) • μ) +
          ∫ x, x ^ 2 ∂((1 / 2 : ℝ≥0∞) • μ.map (fun x : ℝ ↦ -x)) := by
          exact integral_add_measure
            (hsq_int.smul_measure (by simp : (1 / 2 : ℝ≥0∞) ≠ ∞))
            (hsq_map_int.smul_measure (by simp : (1 / 2 : ℝ≥0∞) ≠ ∞))
    _ = (1 / 2 : ℝ) * ∫ x, x ^ 2 ∂μ + (1 / 2 : ℝ) * ∫ x, x ^ 2 ∂μ.map (fun x : ℝ ↦ -x) := by
          rw [integral_smul_measure, integral_smul_measure]
          simp
    _ = (1 / 2 : ℝ) * (1 / (1 - 2 * α)) + (1 / 2 : ℝ) * (1 / (1 - 2 * α)) := by
          simp [hsq, hsq_map]
    _ = 1 / (1 - 2 * α) := by ring

/-- Helper for Example 15.52: the identity map belongs to `L²` for the symmetric Pareto law when
`0 < α < 1 / 2`. -/
lemma memLp_two_id_symmetricParetoMeasure (α : ℝ) (hα0 : 0 < α) (hα_half : α < 1 / 2) :
    MemLp id 2 (symmetricParetoMeasure α) := by
  letI : IsProbabilityMeasure (symmetricParetoMeasure α) :=
    isProbabilityMeasure_symmetricParetoMeasure α hα0
  -- The positive second moment provides the required `L²` integrability.
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 <| Integrable.of_integral_ne_zero ?_
  rw [show (∫ x, id x ^ 2 ∂symmetricParetoMeasure α) =
      ∫ x, x ^ 2 ∂symmetricParetoMeasure α by rfl]
  rw [integral_sq_symmetricParetoMeasure α hα0 hα_half]
  have hpos : 0 < 1 / (1 - 2 * α) := by
    have : 0 < 1 - 2 * α := by linarith
    positivity
  exact ne_of_gt hpos

-- Proof sketch: symmetry makes the first moment vanish. For the second moment, reduce to
-- `2 * ∫_[1,∞) (2 α)⁻¹ x^(1 - 1 / α) dx`, which converges exactly when `α < 1 / 2` and evaluates
-- to `1 / (1 - 2 α)`.
/-- The symmetric Pareto law is centered and has variance `1 / (1 - 2 α)` whenever `0 < α <
1 / 2`. -/
theorem symmetricParetoMeasure_mean_variance (α : ℝ) (hα0 : 0 < α) (hα_half : α < 1 / 2) :
    (∫ x, x ∂symmetricParetoMeasure α) = 0 ∧
      Var[id; symmetricParetoMeasure α] = 1 / (1 - 2 * α) := by
  let μ : Measure ℝ := paretoMeasure 1 (1 / α)
  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_paretoMeasure zero_lt_one (one_div_pos.mpr hα0)
  letI : IsProbabilityMeasure (symmetricParetoMeasure α) :=
    isProbabilityMeasure_symmetricParetoMeasure α hα0
  have hμ_sq :
      ∫ x, x ^ 2 ∂μ = 1 / (1 - 2 * α) :=
    integral_sq_paretoMeasure_one_invAlpha α hα0 hα_half
  have hμ_memLp : MemLp id 2 μ := by
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 <| Integrable.of_integral_ne_zero ?_
    rw [show (∫ x, id x ^ 2 ∂μ) = ∫ x, x ^ 2 ∂μ by rfl]
    rw [hμ_sq]
    have hpos : 0 < 1 / (1 - 2 * α) := by
      have : 0 < 1 - 2 * α := by linarith
      positivity
    exact ne_of_gt hpos
  have hμ_int : Integrable id μ := hμ_memLp.integrable one_le_two
  have hμ_map_int : Integrable id (μ.map (fun x ↦ -x)) := by
    have hμ_neg_int : Integrable (fun x : ℝ ↦ -x) μ := hμ_int.neg
    have hμ_comp_int : Integrable (id ∘ fun x : ℝ ↦ -x) μ := by
      simpa [Function.comp_def] using hμ_neg_int
    exact (integrable_map_equiv (μ := μ) (MeasurableEquiv.neg ℝ) id).2 hμ_comp_int
  have hmean :
      (∫ x, x ∂symmetricParetoMeasure α) = 0 := by
    have hmap_mean :
        ∫ x, x ∂μ.map (fun x : ℝ ↦ -x) = -∫ x, x ∂μ := by
      calc
        ∫ x, x ∂μ.map (fun x : ℝ ↦ -x) = ∫ x, -x ∂μ := by
          simpa using (integral_map_equiv (μ := μ) (MeasurableEquiv.neg ℝ) id)
        _ = -∫ x, x ∂μ := by rw [integral_neg]
    -- The reflected component contributes the negative of the original mean.
    calc
      ∫ x, x ∂symmetricParetoMeasure α
          = ∫ x, x ∂((1 / 2 : ℝ≥0∞) • μ + (1 / 2 : ℝ≥0∞) • μ.map (fun x : ℝ ↦ -x)) := by
              rw [symmetricParetoMeasure_eq_symmetrized_paretoMeasure α]
      _ = ∫ x, x ∂((1 / 2 : ℝ≥0∞) • μ) + ∫ x, x ∂((1 / 2 : ℝ≥0∞) • μ.map (fun x : ℝ ↦ -x)) := by
            exact integral_add_measure
              (hμ_int.smul_measure (by simp : (1 / 2 : ℝ≥0∞) ≠ ∞))
              (hμ_map_int.smul_measure (by simp : (1 / 2 : ℝ≥0∞) ≠ ∞))
      _ = (1 / 2 : ℝ) * ∫ x, x ∂μ + (1 / 2 : ℝ) * ∫ x, x ∂μ.map (fun x : ℝ ↦ -x) := by
            rw [integral_smul_measure, integral_smul_measure]
            simp
      _ = 0 := by rw [hmap_mean]; ring
  have hmemLp : MemLp id 2 (symmetricParetoMeasure α) :=
    memLp_two_id_symmetricParetoMeasure α hα0 hα_half
  have hsq :
      ∫ x, x ^ 2 ∂symmetricParetoMeasure α = 1 / (1 - 2 * α) :=
    integral_sq_symmetricParetoMeasure α hα0 hα_half
  constructor
  · exact hmean
  · -- With zero mean, the variance equals the second moment.
    rw [variance_eq_sub hmemLp]
    simpa [pow_two, hmean] using hsq

-- Proof sketch: transport the expectation and variance identities from the pushforward law
-- `P.map X = symmetricParetoMeasure α` using `hX`, then apply
-- `symmetricParetoMeasure_mean_variance`.
/-- Example 15.52: if a real random variable has distribution with density
`x ↦ (2 α)⁻¹ |x|^(-1 - 1 / α) 1_{|x| ≥ 1}` for some `0 < α < 1 / 2`, then it has mean `0` and
variance `1 / (1 - 2 α)`. -/
theorem hasLaw_symmetricPareto_mean_variance
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (α : ℝ) (hα0 : 0 < α) (hα_half : α < 1 / 2)
    (hX : HasLaw X (symmetricParetoMeasure α) P) :
    P[X] = 0 ∧ Var[X; P] = 1 / (1 - 2 * α) := by
  obtain ⟨hmean, hvar⟩ := symmetricParetoMeasure_mean_variance α hα0 hα_half
  -- Transport expectation and variance through the law equality.
  constructor
  · rw [hX.integral_eq, hmean]
  · rw [hX.variance_eq, hvar]

end
