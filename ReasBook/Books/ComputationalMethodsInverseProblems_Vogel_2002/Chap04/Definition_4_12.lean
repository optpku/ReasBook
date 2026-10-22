/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_12.Covariance
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

public section

noncomputable section

open scoped ProbabilityTheory

namespace ProbabilityTheory

universe u v

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Fintype n]

/-- Definition 4.12 (1). The `i`-th coordinate of the mean vector `μ[X]` is the expectation of
the `i`-th coordinate random variable. -/
theorem mean_apply
    {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n}
    (hX : MeasureTheory.Integrable X μ) (i : n) :
    μ[X] i = μ[fun ω ↦ X ω i] := by
  simpa using (EuclideanSpace.proj i).integral_comp_comm hX |>.symm

end

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v}

/-- Definition 4.12 (2). The `(i, j)` entry of `covarianceMatrix μ X` is the expectation of the
product of the centered coordinate random variables. -/
theorem covarianceMatrix_apply_eq_expectation_centered
    {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n} (i j : n) :
    covarianceMatrix μ X i j =
      μ[fun ω ↦ (X ω i - μ[fun ω ↦ X ω i]) * (X ω j - μ[fun ω ↦ X ω j])] := by
  rw [covarianceMatrix_apply]
  rfl

end

end ProbabilityTheory
