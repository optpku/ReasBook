/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_12.Covariance
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Order.Filter.Extr
public import Mathlib.Probability.Notation

public section

noncomputable section

open scoped Matrix ProbabilityTheory

namespace ProbabilityTheory

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Fintype n]
variable {m : Type w} [Fintype m] [DecidableEq m]

/-- An affine estimator of `X` from `Z` with matrix part `A` and offset `b`. -/
def affineEstimator (A : Matrix n m ℝ) (b : EuclideanSpace ℝ n)
    (Z : Ω → EuclideanSpace ℝ m) : Ω → EuclideanSpace ℝ n :=
  fun ω ↦ b + A.toEuclideanLin (Z ω)

omit [MeasurableSpace Ω] [Fintype n] in
/-- The defining formula for `affineEstimator`. -/
theorem affineEstimator_apply (A : Matrix n m ℝ) (b : EuclideanSpace ℝ n)
    (Z : Ω → EuclideanSpace ℝ m) (ω : Ω) :
    affineEstimator A b Z ω = b + A.toEuclideanLin (Z ω) := by
  simp [affineEstimator]

/-- The minimum-variance linear objective `μ[fun ω ↦ ‖Xhat ω - X ω‖ ^ 2]`. -/
def minimumVarianceLinearObjective (μ : MeasureTheory.Measure Ω)
    (X : Ω → EuclideanSpace ℝ n) (Xhat : Ω → EuclideanSpace ℝ n) : ℝ :=
  μ[fun ω ↦ ‖Xhat ω - X ω‖ ^ 2]

/-- The defining formula for `minimumVarianceLinearObjective`. -/
theorem minimumVarianceLinearObjective_def (μ : MeasureTheory.Measure Ω)
    (X : Ω → EuclideanSpace ℝ n) (Xhat : Ω → EuclideanSpace ℝ n) :
    minimumVarianceLinearObjective μ X Xhat = μ[fun ω ↦ ‖Xhat ω - X ω‖ ^ 2] := by
  simp [minimumVarianceLinearObjective]

/-- The admissible class of affine estimators of `Z` with finite second moment. -/
def minimumVarianceLinearAdmissibleSet (μ : MeasureTheory.Measure Ω)
    (Z : Ω → EuclideanSpace ℝ m) :
    Set (Ω → EuclideanSpace ℝ n) :=
  { Xhat | ∃ A : Matrix n m ℝ, ∃ b : EuclideanSpace ℝ n,
      Xhat = affineEstimator A b Z ∧ MeasureTheory.MemLp Xhat 2 μ }

set_option linter.unusedDecidableInType false in
/-- Membership in `minimumVarianceLinearAdmissibleSet` means being an affine estimator of `Z`
with finite second moment. -/
theorem mem_minimumVarianceLinearAdmissibleSet_iff (μ : MeasureTheory.Measure Ω)
    (Z : Ω → EuclideanSpace ℝ m) (Xhat : Ω → EuclideanSpace ℝ n) :
    Xhat ∈ minimumVarianceLinearAdmissibleSet μ Z ↔
      ∃ A : Matrix n m ℝ, ∃ b : EuclideanSpace ℝ n,
        Xhat = affineEstimator A b Z ∧ MeasureTheory.MemLp Xhat 2 μ := Iff.rfl

/-- A candidate estimator is minimum-variance linear when it is admissible and minimizes
`minimumVarianceLinearObjective μ X` on the admissible class. -/
structure IsMinimumVarianceLinearEstimator
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → EuclideanSpace ℝ n) (Z : Ω → EuclideanSpace ℝ m)
    (Xhat : Ω → EuclideanSpace ℝ n) : Prop where
  /-- The estimator belongs to the admissible affine class. -/
  mem_admissible : Xhat ∈ minimumVarianceLinearAdmissibleSet μ Z
  /-- The estimator minimizes the mean squared error on the admissible class. -/
  optimal : IsMinOn (minimumVarianceLinearObjective μ X)
    (minimumVarianceLinearAdmissibleSet μ Z) Xhat

namespace IsMinimumVarianceLinearEstimator

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- Construct a minimum-variance linear-estimator certificate from admissibility and optimality
data. -/
theorem ofMemOptimal (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → EuclideanSpace ℝ n) (Z : Ω → EuclideanSpace ℝ m)
    (Xhat : Ω → EuclideanSpace ℝ n)
    (h_mem : Xhat ∈ minimumVarianceLinearAdmissibleSet μ Z)
    (h_opt : IsMinOn (minimumVarianceLinearObjective μ X)
      (minimumVarianceLinearAdmissibleSet μ Z) Xhat) :
    IsMinimumVarianceLinearEstimator μ X Z Xhat :=
  ⟨h_mem, h_opt⟩

end IsMinimumVarianceLinearEstimator

set_option linter.unusedDecidableInType false in
/-- The structure `IsMinimumVarianceLinearEstimator μ X Z Xhat` is equivalent to admissibility of
`Xhat` together with optimality for `minimumVarianceLinearObjective μ X`. -/
theorem isMinimumVarianceLinearEstimator_iff (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (X : Ω → EuclideanSpace ℝ n)
    (Z : Ω → EuclideanSpace ℝ m) (Xhat : Ω → EuclideanSpace ℝ n) :
    IsMinimumVarianceLinearEstimator μ X Z Xhat ↔
      Xhat ∈ minimumVarianceLinearAdmissibleSet μ Z ∧
        IsMinOn (minimumVarianceLinearObjective μ X)
          (minimumVarianceLinearAdmissibleSet μ Z) Xhat := by
  constructor
  · intro h
    -- Unpack the structure fields into the corresponding conjunction.
    exact ⟨h.mem_admissible, h.optimal⟩
  · rintro ⟨h_mem, h_opt⟩
    -- Repackage admissibility and optimality into the structure certificate.
    exact ⟨h_mem, h_opt⟩

/-- The centered affine covariance formula from Proposition 4.35. -/
def covarianceFormulaEstimator (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → EuclideanSpace ℝ n) (Z : Ω → EuclideanSpace ℝ m) :
    Ω → EuclideanSpace ℝ n :=
  fun ω ↦ μ[X] +
    (crossCovarianceMatrix μ X Z * (covarianceMatrix μ Z)⁻¹).toEuclideanLin (Z ω - μ[Z])

/-- The defining formula for `covarianceFormulaEstimator`. -/
theorem covarianceFormulaEstimator_apply (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (X : Ω → EuclideanSpace ℝ n)
    (Z : Ω → EuclideanSpace ℝ m) (ω : Ω) :
    covarianceFormulaEstimator μ X Z ω = μ[X] +
      (crossCovarianceMatrix μ X Z * (covarianceMatrix μ Z)⁻¹).toEuclideanLin (Z ω - μ[Z]) := by
  simp [covarianceFormulaEstimator]

end

end ProbabilityTheory
