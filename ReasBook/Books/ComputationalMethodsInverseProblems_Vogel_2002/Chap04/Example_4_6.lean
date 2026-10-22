/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.CDF
public import Mathlib.Probability.HasLaw

public section

namespace FairDial

universe u

/-- Example 4.6 (1). A fair dial angle has law
`ProbabilityTheory.cond MeasureTheory.volume (Set.Icc 0 (2 * Real.pi))` when it is uniformly
distributed on `Set.Icc 0 (2 * Real.pi)`. -/
theorem hasLaw
    {Ω : Type u} [MeasurableSpace Ω] {ℙ : MeasureTheory.Measure Ω} {X : Ω → ℝ}
    (hX : MeasureTheory.pdf.IsUniform X (Set.Icc 0 (2 * Real.pi)) ℙ) :
    ProbabilityTheory.HasLaw X
      (ProbabilityTheory.cond MeasureTheory.volume (Set.Icc 0 (2 * Real.pi))) ℙ := by
  refine
    { aemeasurable := ?_
      map_eq := hX }
  have hIcc_ne_zero : MeasureTheory.volume (Set.Icc 0 (2 * Real.pi)) ≠ 0 := by
    rw [Real.volume_Icc, sub_zero]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hIcc_ne_top : MeasureTheory.volume (Set.Icc 0 (2 * Real.pi)) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  exact hX.aemeasurable hIcc_ne_zero hIcc_ne_top

/-- Example 4.6 (2). The cumulative distribution function of a fair dial angle is
`0` for `x < 0`, `x / (2 * Real.pi)` for `0 ≤ x < 2 * Real.pi`, and `1` for
`x ≥ 2 * Real.pi`. -/
theorem cdf_eq
    {Ω : Type u} [MeasurableSpace Ω] {ℙ : MeasureTheory.Measure Ω} {X : Ω → ℝ}
    (hX : MeasureTheory.pdf.IsUniform X (Set.Icc 0 (2 * Real.pi)) ℙ) (x : ℝ) :
    ProbabilityTheory.cdf (MeasureTheory.Measure.map X ℙ) x =
      if x < 0 then 0 else if x < 2 * Real.pi then x / (2 * Real.pi) else 1 := by
  have htwo_pi_nonneg : 0 ≤ 2 * Real.pi := by positivity
  have hIcc_ne_zero : MeasureTheory.volume (Set.Icc 0 (2 * Real.pi)) ≠ 0 := by
    rw [Real.volume_Icc, sub_zero]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hIcc_ne_top : MeasureTheory.volume (Set.Icc 0 (2 * Real.pi)) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hprob :
      MeasureTheory.IsProbabilityMeasure
        (ProbabilityTheory.cond MeasureTheory.volume (Set.Icc 0 (2 * Real.pi))) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hIcc_ne_zero hIcc_ne_top
  have hcdf :
      ProbabilityTheory.cdf
          (ProbabilityTheory.cond MeasureTheory.volume (Set.Icc 0 (2 * Real.pi))) x =
        (ProbabilityTheory.cond MeasureTheory.volume
          (Set.Icc 0 (2 * Real.pi))).real (Set.Iic x) := by
    simpa using
      (@ProbabilityTheory.cdf_eq_real
        (ProbabilityTheory.cond MeasureTheory.volume (Set.Icc 0 (2 * Real.pi))) hprob x)
  rw [show MeasureTheory.Measure.map X ℙ =
      ProbabilityTheory.cond MeasureTheory.volume (Set.Icc 0 (2 * Real.pi)) from hX]
  rw [hcdf, MeasureTheory.measureReal_def, ProbabilityTheory.cond_apply measurableSet_Icc]
  by_cases hx0 : x < 0
  · have h_inter : Set.Icc 0 (2 * Real.pi) ∩ Set.Iic x = ∅ := by
      have hx0' : ¬ 0 ≤ x := not_le.mpr hx0
      ext y
      constructor
      · intro hy
        exact (hx0' <| le_trans hy.1.1 hy.2).elim
      · intro hy
        simp at hy
    rw [if_pos hx0, h_inter]
    simp
  · by_cases hxp : x < 2 * Real.pi
    · have hx_nonneg : 0 ≤ x := le_of_not_gt hx0
      have h_inter : Set.Icc 0 (2 * Real.pi) ∩ Set.Iic x = Set.Icc 0 x := by
        ext y
        constructor
        · intro hy
          exact ⟨hy.1.1, hy.2⟩
        · intro hy
          exact ⟨⟨hy.1, hy.2.trans hxp.le⟩, hy.2⟩
      rw [if_neg hx0, if_pos hxp]
      rw [h_inter, Real.volume_Icc, Real.volume_Icc, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal (show 0 ≤ 2 * Real.pi - 0 by simpa using htwo_pi_nonneg),
        ENNReal.toReal_ofReal (show 0 ≤ x - 0 by simpa using hx_nonneg), sub_zero, sub_zero]
      simp [div_eq_mul_inv, mul_comm]
    · have hxp' : 2 * Real.pi ≤ x := le_of_not_gt hxp
      have h_inter : Set.Icc 0 (2 * Real.pi) ∩ Set.Iic x = Set.Icc 0 (2 * Real.pi) := by
        ext y
        constructor
        · intro hy
          exact hy.1
        · intro hy
          exact ⟨hy, hy.2.trans hxp'⟩
      rw [if_neg hx0, if_neg hxp]
      rw [h_inter, Real.volume_Icc, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal (show 0 ≤ 2 * Real.pi - 0 by simpa using htwo_pi_nonneg), sub_zero]
      field_simp [Real.pi_ne_zero]

/-- Example 4.6 (3). The fair dial density is `(2 * Real.pi)⁻¹` on
`0 < x ∧ x < 2 * Real.pi` and `0` elsewhere, as an a.e. equality with respect
to `MeasureTheory.volume`. -/
theorem pdf_toReal_ae_eq
    {Ω : Type u} [MeasurableSpace Ω] {ℙ : MeasureTheory.Measure Ω} {X : Ω → ℝ}
    (hX : MeasureTheory.pdf.IsUniform X (Set.Icc 0 (2 * Real.pi)) ℙ) :
    (fun x : ℝ ↦ (MeasureTheory.pdf X ℙ MeasureTheory.volume x).toReal) =ᵐ[MeasureTheory.volume]
      fun x ↦ if 0 < x ∧ x < 2 * Real.pi then (2 * Real.pi)⁻¹ else 0 := by
  have htwo_pi_nonneg : 0 ≤ 2 * Real.pi := by positivity
  have hconst :
      ((MeasureTheory.volume (Set.Icc 0 (2 * Real.pi)))⁻¹).toReal = (2 * Real.pi)⁻¹ := by
    rw [Real.volume_Icc, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (show 0 ≤ 2 * Real.pi - 0 by simpa using htwo_pi_nonneg), sub_zero]
  filter_upwards
    [hX.pdf_toReal_ae_eq measurableSet_Icc,
      (show Set.Icc 0 (2 * Real.pi) =ᵐ[MeasureTheory.volume] Set.Ioo 0 (2 * Real.pi) from
        (MeasureTheory.Ioo_ae_eq_Icc
          : Set.Ioo (0 : ℝ) (2 * Real.pi) =ᵐ[MeasureTheory.volume] Set.Icc 0 (2 * Real.pi)).symm)]
      with x hxpdf hxset
  rw [hxpdf]
  by_cases hmem : x ∈ Set.Ioo 0 (2 * Real.pi)
  · have hmem' : x ∈ Set.Icc 0 (2 * Real.pi) := by
      exact Eq.mpr hxset hmem
    have hpi_nonneg : 0 ≤ Real.pi := by positivity
    rw [Set.indicator_of_mem hmem']
    rw [if_pos (by simpa [Set.mem_Ioo] using hmem)]
    simp [Pi.smul_apply, hpi_nonneg]
  · have hmem' : x ∉ Set.Icc 0 (2 * Real.pi) := by
      intro hxIcc
      exact hmem (Eq.mp hxset hxIcc)
    rw [Set.indicator_of_notMem hmem']
    rw [if_neg (by simpa [Set.mem_Ioo] using hmem)]
    simp

end FairDial
