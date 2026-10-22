/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_15.Likelihood
public import Mathlib.Probability.Distributions.Gaussian.Real

public section

noncomputable section

open scoped BigOperators

namespace GaussianLikelihood

universe u

section

variable {ι : Type u} [Fintype ι]

/-- The arithmetic mean of a finite nonempty observed real sample. -/
def sampleMean (d : ι → ℝ) : ℝ :=
  (∑ i, d i) / Fintype.card ι

/-- The defining finite-sum formula for `sampleMean`. -/
theorem sampleMean_def (d : ι → ℝ) :
    sampleMean d = (∑ i, d i) / Fintype.card ι := by
  rfl

/-- The average squared deviation of a finite nonempty observed sample from the specified mean. -/
def centeredSquareAverage (mean : ℝ) (d : ι → ℝ) : ℝ :=
  (∑ i, (d i - mean) ^ 2) / Fintype.card ι

/-- The defining finite-sum formula for `centeredSquareAverage`. -/
theorem centeredSquareAverage_def (mean : ℝ) (d : ι → ℝ) :
    centeredSquareAverage mean d = (∑ i, (d i - mean) ^ 2) / Fintype.card ι := by
  rfl

end

section

variable {ι : Type u} [Fintype ι]

/-- The finite-product Gaussian likelihood of an observed sample under a common mean and
variance. Outside the positive-variance regime, the likelihood is set to `0`. -/
def gaussianLikelihood (d : ι → ℝ) (mean variance : ℝ) : ℝ :=
  if hvariance : 0 < variance then
    ∏ i, ProbabilityTheory.gaussianPDFReal mean ⟨variance, le_of_lt hvariance⟩ (d i)
  else
    0

/-- The defining finite-product formula for `gaussianLikelihood`. -/
theorem gaussianLikelihood_def (d : ι → ℝ) (mean variance : ℝ) :
    gaussianLikelihood d mean variance =
      if hvariance : 0 < variance then
        ∏ i, ProbabilityTheory.gaussianPDFReal mean ⟨variance, le_of_lt hvariance⟩ (d i)
      else
        0 := by
  rfl

end

end GaussianLikelihood
