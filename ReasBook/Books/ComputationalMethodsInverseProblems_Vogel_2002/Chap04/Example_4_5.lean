/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_2.DiscreteRandomVariable
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_5.FairCoin
public import Mathlib.Probability.CDF
import Mathlib.Tactic.NormNum

public section

noncomputable section

open scoped ENNReal ProbabilityTheory

namespace FairCoin

/-- Helper for Example 4.5: the fair-coin `0/1` random variable `value` is discrete under
`pmf.toMeasure`. -/
theorem isDiscreteRandomVariable_value :
    ProbabilityTheory.IsDiscreteRandomVariable pmf.toMeasure value := by
  -- The support file already provides the law of `value`, so that law is the discrete witness.
  exact ProbabilityTheory.isDiscreteRandomVariable_iff.mpr ⟨valuePmf, hasLaw_value⟩

/-- The canonical discrete probability mass function attached to `value` is `valuePmf`. -/
theorem discretePmf_eq_valuePmf :
    ProbabilityTheory.discretePmf isDiscreteRandomVariable_value = valuePmf := by
  -- Compare the two laws of `value` under `pmf.toMeasure` and use injectivity of `PMF.toMeasure`.
  apply PMF.toMeasure_injective
  exact
    (ProbabilityTheory.discretePmf_spec isDiscreteRandomVariable_value).map_eq.symm.trans
      hasLaw_value.map_eq

/-- Helper for Example 4.5: the fair-coin probability mass function is `1 / 2` at `0` and `1`,
and `0` elsewhere. -/
theorem valuePmf_apply (x : ℝ) :
    valuePmf x = if x = 0 then (1 / 2 : ℝ≥0∞) else if x = 1 then (1 / 2 : ℝ≥0∞) else 0 := by
  -- Split according to the two support points of the fair-coin `0/1` law.
  by_cases hx0 : x = 0
  · subst hx0
    simp
  · by_cases hx1 : x = 1
    · subst hx1
      simp [hx0]
    · rw [valuePmf_eq_zero_of_ne_zero_ne_one hx0 hx1]
      simp [hx0, hx1]

/-- The fair-coin probability mass at `0` is `1 / 2`. -/
@[simp] theorem valuePmf_apply_zero :
    valuePmf 0 = (1 / 2 : ℝ≥0∞) := by
  simp [valuePmf_apply]

/-- The fair-coin probability mass at `1` is `1 / 2`. -/
@[simp] theorem valuePmf_apply_one :
    valuePmf 1 = (1 / 2 : ℝ≥0∞) := by
  simp [valuePmf_apply]

/-- The fair-coin probability mass vanishes away from `0` and `1`. -/
theorem valuePmf_apply_of_ne_zero_of_ne_one {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    valuePmf x = 0 := by
  simp [valuePmf_apply, hx0, hx1]

/-- Helper for Example 4.5: the Bernoulli parameter of the fair-coin law is `1 / 2`. -/
private theorem fairProb_eq_half : (fairProb : ℝ) = 1 / 2 := by
  -- Identify the Bernoulli parameter through the mass of the singleton `{1}`.
  calc
    (fairProb : ℝ) = Ber((1 : ℝ), 0, fairProb).real {1} := by
      symm
      rw [ProbabilityTheory.bernoulliMeasure_real_apply fairProb
        (measurableSet_singleton (1 : ℝ))]
      simp
    _ = valuePmf.toMeasure.real {1} := by
      rw [← valuePmf_toMeasure_eq]
    _ = 1 / 2 := by
      rw [MeasureTheory.measureReal_def,
        valuePmf.toMeasure_apply_singleton 1 (measurableSet_singleton 1), valuePmf_one]
      norm_num

/-- Helper for Example 4.5: the cumulative distribution function of the fair-coin `0/1` law is
`0` for `x < 0`, `1 / 2` for `0 ≤ x < 1`, and `1` for `x ≥ 1`. -/
theorem cdf_eq (x : ℝ) :
    ProbabilityTheory.cdf valuePmf.toMeasure x =
      if x < 0 then 0 else if x < 1 then 1 / 2 else 1 := by
  have hcdf :
      ProbabilityTheory.cdf valuePmf.toMeasure x = valuePmf.toMeasure.real (Set.Iic x) := by
    -- Rewrite the cdf as the probability of the interval `(-∞, x]`.
    simpa using (@ProbabilityTheory.cdf_eq_real valuePmf.toMeasure inferInstance x)
  rw [hcdf, valuePmf_toMeasure_eq]
  by_cases hx0 : x < 0
  · have h1 : (1 : ℝ) ∉ Set.Iic x := by
      simp [Set.mem_Iic, not_le.mpr (lt_trans hx0 zero_lt_one)]
    have h0 : (0 : ℝ) ∉ Set.Iic x := by
      simp [Set.mem_Iic, not_le.mpr hx0]
    rw [if_pos hx0]
    -- Below `0`, neither atom belongs to `Set.Iic x`, so the Bernoulli mass is zero.
    simpa using
      (ProbabilityTheory.bernoulliMeasure_real_apply_of_notMem_of_notMem
        (x := (1 : ℝ)) (y := 0) fairProb measurableSet_Iic h1 h0)
  · by_cases hx1 : x < 1
    · have h1 : (1 : ℝ) ∉ Set.Iic x := by
        simp [Set.mem_Iic, not_le.mpr hx1]
      have h0 : (0 : ℝ) ∈ Set.Iic x := by
        simp [Set.mem_Iic, le_of_not_gt hx0]
      rw [if_neg hx0, if_pos hx1]
      -- Between `0` and `1`, only the atom at `0` lies in `Set.Iic x`.
      calc
        Ber(1, 0, fairProb).real (Set.Iic x) = 1 - (fairProb : ℝ) := by
          simpa using
            (ProbabilityTheory.bernoulliMeasure_real_apply_of_notMem_of_mem
              (x := (1 : ℝ)) (y := 0) fairProb measurableSet_Iic h1 h0)
        _ = 1 / 2 := by
          rw [fairProb_eq_half]
          norm_num
    · have h1 : (1 : ℝ) ∈ Set.Iic x := by
        simp [Set.mem_Iic, le_of_not_gt hx1]
      have h0 : (0 : ℝ) ∈ Set.Iic x := by
        simp [Set.mem_Iic, le_of_not_gt hx0]
      rw [if_neg hx0, if_neg hx1]
      -- From `1` onward, both atoms belong to `Set.Iic x`, so the cdf is `1`.
      simpa using
        (ProbabilityTheory.bernoulliMeasure_real_apply_of_mem_of_mem
          (x := (1 : ℝ)) (y := 0) fairProb measurableSet_Iic h1 h0)

/-- Example 4.5. The expected value of the fair-coin `0/1` random variable under `pmf.toMeasure`
is `1 / 2`. -/
theorem expectation_eq :
    pmf.toMeasure[value] = 1 / 2 := by
  -- Transport the expectation to the law of `value`.
  rw [hasLaw_value.integral_eq, valuePmf_toMeasure_eq]
  -- Evaluate the Bernoulli integral and substitute the fair-coin parameter.
  calc
    ∫ z : ℝ, z ∂Ber(1, 0, fairProb) =
        (fairProb : ℝ) * 1 + (1 - (fairProb : ℝ)) * 0 := by
      simpa [smul_eq_mul] using
        (ProbabilityTheory.integral_bernoulliMeasure
          (x := (1 : ℝ)) (y := 0) fairProb (f := fun z : ℝ ↦ z))
    _ = 1 / 2 := by
      rw [fairProb_eq_half]
      norm_num

/-- The expectation statement of Example 4.5 expressed on the induced law `valuePmf.toMeasure`. -/
theorem integral_valuePmf_eq :
    ∫ x : ℝ, x ∂valuePmf.toMeasure = 1 / 2 := by
  -- Reuse the law-transport identity already used in the expectation computation.
  simpa [hasLaw_value.integral_eq] using expectation_eq

end FairCoin
