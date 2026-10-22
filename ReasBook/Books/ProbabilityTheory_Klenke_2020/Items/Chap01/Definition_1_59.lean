/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Filter ProbabilityTheory

/-- A defective distribution function on `ℝ` is a Stieltjes function with values in `[0, 1]`
and limit `0` at `-∞`. -/
class IsDefectiveDistributionFunction (F : StieltjesFunction ℝ) : Prop where
  nonneg : ∀ x : ℝ, 0 ≤ F x
  le_one : ∀ x : ℝ, F x ≤ 1
  tendsto_atBot_zero : Tendsto F atBot (nhds 0)

/-- Definition 1.59: A probability distribution function on `ℝ` is a Stieltjes function with
values in `[0, 1]`, limit `0` at `-∞`, and limit `1` at `+∞`. -/
class IsDistributionFunction (F : StieltjesFunction ℝ) : Prop extends
    IsDefectiveDistributionFunction F where
  tendsto_atTop_one : Tendsto F atTop (nhds 1)

/-- A defective distribution function induces a finite Lebesgue--Stieltjes measure. -/
instance (F : StieltjesFunction ℝ) [hF : IsDefectiveDistributionFunction F] :
    IsFiniteMeasure F.measure := by
  have h_abs : ∀ x, |F x| ≤ (1 : ℝ) := fun x ↦ by
    rw [abs_of_nonneg (hF.nonneg x)]
    exact hF.le_one x
  exact F.isFiniteMeasure_of_forall_abs_le h_abs

/-- A distribution function induces a probability measure via its Lebesgue--Stieltjes measure. -/
instance (F : StieltjesFunction ℝ) [hF : IsDistributionFunction F] :
    IsProbabilityMeasure F.measure :=
  F.isProbabilityMeasure hF.toIsDefectiveDistributionFunction.tendsto_atBot_zero
    hF.tendsto_atTop_one

/- The distribution function attached to a real probability measure is the canonical cdf
`ProbabilityTheory.cdf`. -/
recall ProbabilityTheory.cdf

/- For a real probability measure, the canonical cdf is the interval-mass function
`x ↦ μ.real (Set.Iic x)`. -/
recall ProbabilityTheory.cdf_eq_real

/-- The canonical cdf of a real probability measure is a distribution function. -/
instance instIsDistributionFunction_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsDistributionFunction (cdf μ) where
  toIsDefectiveDistributionFunction :=
    { nonneg := cdf_nonneg μ
      le_one := cdf_le_one μ
      tendsto_atBot_zero := tendsto_cdf_atBot μ }
  tendsto_atTop_one := tendsto_cdf_atTop μ
