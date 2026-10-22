/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.Moments.Covariance

public section

noncomputable section

open scoped ProbabilityTheory

namespace ProbabilityTheory

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v}
variable {m : Type w}

/-- The centered covariance matrix of a finite real random vector, with entries
`cov[fun ω ↦ X ω i, fun ω ↦ X ω j; μ]`. -/
def covarianceMatrix (μ : MeasureTheory.Measure Ω) (X : Ω → EuclideanSpace ℝ n) :
    Matrix n n ℝ :=
  fun i j ↦ cov[fun ω ↦ X ω i, fun ω ↦ X ω j; μ]

/-- The entries of `covarianceMatrix μ X` are the coordinatewise centered covariances of `X`. -/
theorem covarianceMatrix_apply {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n}
    (i j : n) :
    covarianceMatrix μ X i j = cov[fun ω ↦ X ω i, fun ω ↦ X ω j; μ] := by
  simp [covarianceMatrix]

/-- The centered cross-covariance matrix of finite real random vectors `X` and `Z`, with entries
`cov[fun ω ↦ X ω i, fun ω ↦ Z ω j; μ]`. -/
def crossCovarianceMatrix (μ : MeasureTheory.Measure Ω) (X : Ω → EuclideanSpace ℝ n)
    (Z : Ω → EuclideanSpace ℝ m) : Matrix n m ℝ :=
  fun i j ↦ cov[fun ω ↦ X ω i, fun ω ↦ Z ω j; μ]

/-- The entries of `crossCovarianceMatrix μ X Z` are the coordinatewise centered covariances of
`X` against `Z`. -/
theorem crossCovarianceMatrix_apply {μ : MeasureTheory.Measure Ω}
    {X : Ω → EuclideanSpace ℝ n} {Z : Ω → EuclideanSpace ℝ m} (i : n) (j : m) :
    crossCovarianceMatrix μ X Z i j = cov[fun ω ↦ X ω i, fun ω ↦ Z ω j; μ] := by
  simp [crossCovarianceMatrix]

end

end ProbabilityTheory
