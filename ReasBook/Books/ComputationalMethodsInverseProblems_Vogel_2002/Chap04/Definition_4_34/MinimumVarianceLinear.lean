/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_31.LinearEstimator
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Order.Filter.Extr
public import Mathlib.Probability.Notation

public section

noncomputable section

open scoped ProbabilityTheory

namespace ProbabilityTheory
namespace MinimumVarianceLinear

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Fintype n]
variable {m : Type w} [Fintype m] [DecidableEq m]

/-- The mean-squared error objective `μ[fun ω ↦ ‖linearEstimator B Z ω - X ω‖ ^ 2]` for the
coefficient matrix `B`. -/
def coefficientObjective (μ : MeasureTheory.Measure Ω)
    (X : Ω → EuclideanSpace ℝ n) (Z : Ω → EuclideanSpace ℝ m) (B : Matrix n m ℝ) : ℝ :=
  μ[fun ω ↦ ‖linearEstimator B Z ω - X ω‖ ^ 2]

/-- The defining formula for `ProbabilityTheory.MinimumVarianceLinear.coefficientObjective`. -/
theorem coefficientObjective_def (μ : MeasureTheory.Measure Ω)
    (X : Ω → EuclideanSpace ℝ n) (Z : Ω → EuclideanSpace ℝ m) (B : Matrix n m ℝ) :
    coefficientObjective μ X Z B = μ[fun ω ↦ ‖linearEstimator B Z ω - X ω‖ ^ 2] := by
  simp [coefficientObjective]

/-- The finite-second-moment hypotheses on the target random vector `X` and the observed random
vector `Z` from Definition 4.34. -/
def HasFiniteSecondMoments (μ : MeasureTheory.Measure Ω)
    (X : Ω → EuclideanSpace ℝ n) (Z : Ω → EuclideanSpace ℝ m) : Prop :=
  MeasureTheory.MemLp X 2 μ ∧ MeasureTheory.MemLp Z 2 μ

omit [DecidableEq m] in
/-- The defining characterization of
`ProbabilityTheory.MinimumVarianceLinear.HasFiniteSecondMoments`. -/
theorem hasFiniteSecondMoments_iff (μ : MeasureTheory.Measure Ω)
    (X : Ω → EuclideanSpace ℝ n) (Z : Ω → EuclideanSpace ℝ m) :
    HasFiniteSecondMoments μ X Z ↔
      MeasureTheory.MemLp X 2 μ ∧ MeasureTheory.MemLp Z 2 μ :=
  Iff.rfl

/-- Under the finite-second-moment hypotheses of Definition 4.34, a coefficient matrix is
optimal when it minimizes the mean-squared prediction error over all real coefficient matrices. -/
def IsOptimalCoefficient (μ : MeasureTheory.Measure Ω) (X : Ω → EuclideanSpace ℝ n)
    (Z : Ω → EuclideanSpace ℝ m) (B : Matrix n m ℝ) : Prop :=
  HasFiniteSecondMoments μ X Z ∧ IsMinOn (coefficientObjective μ X Z) Set.univ B

/-- `ProbabilityTheory.MinimumVarianceLinear.IsOptimalCoefficient μ X Z B` means that `B`
packages the finite-second-moment hypotheses on `X` and `Z` together with the statement that `B`
minimizes `coefficientObjective μ X Z` on `Set.univ`. -/
theorem isOptimalCoefficient_iff (μ : MeasureTheory.Measure Ω)
    (X : Ω → EuclideanSpace ℝ n) (Z : Ω → EuclideanSpace ℝ m) (B : Matrix n m ℝ) :
    IsOptimalCoefficient μ X Z B ↔
      HasFiniteSecondMoments μ X Z ∧ IsMinOn (coefficientObjective μ X Z) Set.univ B :=
  Iff.rfl

/-- An optimal coefficient for Definition 4.34 can be formed only under the finite-second-moment
hypotheses on `X` and `Z`. -/
theorem IsOptimalCoefficient.hasFiniteSecondMoments
    {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n}
    {Z : Ω → EuclideanSpace ℝ m} {B : Matrix n m ℝ}
    (h : IsOptimalCoefficient μ X Z B) :
    HasFiniteSecondMoments μ X Z :=
  h.1

/-- The optimality component of `ProbabilityTheory.MinimumVarianceLinear.IsOptimalCoefficient`. -/
theorem IsOptimalCoefficient.isMinOn
    {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n}
    {Z : Ω → EuclideanSpace ℝ m} {B : Matrix n m ℝ}
    (h : IsOptimalCoefficient μ X Z B) :
    IsMinOn (coefficientObjective μ X Z) Set.univ B :=
  h.2

/-- Definition 4.34. Under the finite-second-moment hypotheses on `X` and `Z`, an estimator
`Xhat` is a minimum variance linear estimator of `X` from `Z` when it is `linearEstimator B Z`
for some optimal coefficient matrix `B`. -/
def IsEstimator (μ : MeasureTheory.Measure Ω) (X : Ω → EuclideanSpace ℝ n)
    (Z : Ω → EuclideanSpace ℝ m) (Xhat : Ω → EuclideanSpace ℝ n) : Prop :=
  ∃ B : Matrix n m ℝ, Xhat = linearEstimator B Z ∧ IsOptimalCoefficient μ X Z B

/-- `ProbabilityTheory.MinimumVarianceLinear.IsEstimator μ X Z Xhat` is equivalent to the
existence of an optimal coefficient matrix `B` with `Xhat = linearEstimator B Z`; in particular,
the finite-second-moment hypotheses on `X` and `Z` are part of the certificate. -/
theorem isEstimator_iff (μ : MeasureTheory.Measure Ω) (X : Ω → EuclideanSpace ℝ n)
    (Z : Ω → EuclideanSpace ℝ m) (Xhat : Ω → EuclideanSpace ℝ n) :
    IsEstimator μ X Z Xhat ↔
      ∃ B : Matrix n m ℝ, Xhat = linearEstimator B Z ∧ IsOptimalCoefficient μ X Z B := Iff.rfl

/-- A minimum variance linear estimator of `X` from `Z` carries the finite-second-moment
hypotheses on `X` and `Z`. -/
theorem IsEstimator.hasFiniteSecondMoments
    {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n}
    {Z : Ω → EuclideanSpace ℝ m} {Xhat : Ω → EuclideanSpace ℝ n}
    (h : IsEstimator μ X Z Xhat) :
    HasFiniteSecondMoments μ X Z := by
  rcases h with ⟨B, rfl, hB⟩
  exact hB.hasFiniteSecondMoments

end

end MinimumVarianceLinear
end ProbabilityTheory
