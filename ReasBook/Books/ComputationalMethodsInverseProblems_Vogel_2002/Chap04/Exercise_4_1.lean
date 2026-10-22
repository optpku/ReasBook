/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_12.Covariance
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Moments.Variance

public section

noncomputable section

namespace ProbabilityTheory

universe u v

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Finite n]

/-- exercise_4_1 (1). Exercise 4.1. The covariance matrix `covarianceMatrix μ X`
of a finite real random vector is symmetric. -/
theorem covarianceMatrix_isSymm
    {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n} :
    Matrix.IsSymm (covarianceMatrix μ X) := by
  -- Local instance justification (proof-local temporary datum): `covarianceMatrix_apply`
  -- and matrix extensionality use a `Fintype` index, while the public theorem only needs
  -- finiteness of the coordinate type.
  let _ := Fintype.ofFinite n
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  rw [covarianceMatrix_apply, covarianceMatrix_apply, covariance_comm]

omit [Finite n] in
/-- Helper for Exercise 4.1: a finitely supported linear combination of the coordinates of `X`
stays in `L²(μ)` when every coordinate of `X` does. -/
lemma coordinateLinearCombination_memLp
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n}
    (hX : ∀ i, MeasureTheory.MemLp (fun ω ↦ X ω i) 2 μ)
    (x : n →₀ ℝ) :
    MeasureTheory.MemLp (∑ i ∈ x.support, fun ω ↦ x i * X ω i) 2 μ := by
  -- Sum the coordinatewise `L²` bounds over the finite support of `x`.
  exact MeasureTheory.memLp_finsetSum' (s := x.support)
    (f := fun i ω ↦ x i * X ω i) fun i hi ↦ (hX i).const_mul (x i)

omit [Finite n] in
/-- Helper for Exercise 4.1: the quadratic form of `covarianceMatrix μ X` along `x`
is the self-covariance of the scalar random variable `ω ↦ ∑ i in x.support, x i * X ω i`. -/
lemma covarianceMatrixQuadraticForm_eq_covariance
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n}
    (hX : ∀ i, MeasureTheory.MemLp (fun ω ↦ X ω i) 2 μ)
    (x : n →₀ ℝ) :
    x.sum (fun i xi ↦ x.sum (fun j xj ↦ star xi * covarianceMatrix μ X i j * xj)) =
      cov[∑ i ∈ x.support, fun ω ↦ x i * X ω i,
        ∑ i ∈ x.support, fun ω ↦ x i * X ω i; μ] := by
  classical
  -- First expand the `Finsupp` quadratic form to a support-indexed double sum.
  calc
    x.sum (fun i xi ↦ x.sum (fun j xj ↦ star xi * covarianceMatrix μ X i j * xj))
        = x.support.sum fun i ↦ x.support.sum fun j ↦
            (x i * covarianceMatrix μ X i j) * x j := by
            simp [Finsupp.sum]
    _ = x.support.sum fun i ↦ x.support.sum fun j ↦
          cov[fun ω ↦ x i * X ω i, fun ω ↦ x j * X ω j; μ] := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [covariance_const_mul_left, covariance_const_mul_right, covarianceMatrix_apply]
            ring
    -- Then collapse the double covariance sum back to one covariance of finite sums.
    _ = cov[∑ i ∈ x.support, fun ω ↦ x i * X ω i,
          ∑ i ∈ x.support, fun ω ↦ x i * X ω i; μ] := by
            symm
            rw [covariance_sum_sum'
              (X := fun i ω ↦ x i * X ω i)
              (Y := fun i ω ↦ x i * X ω i)
              (s := x.support)
              (t := x.support)
              (fun i _ ↦ (hX i).const_mul (x i))
              (fun i _ ↦ (hX i).const_mul (x i))]

/-- Helper for Exercise 4.1: the covariance of a real random variable with itself is
nonnegative once the variable has finite second moment. -/
lemma selfCovariance_nonneg_of_memLp
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY : MeasureTheory.MemLp Y 2 μ) :
    0 ≤ cov[Y, Y; μ] := by
  -- Rewrite self-covariance as variance, where nonnegativity is built in.
  rw [ProbabilityTheory.covariance_self hY.aemeasurable]
  exact ProbabilityTheory.variance_nonneg Y μ

/-- Exercise 4.1. Under a probability measure, if each coordinate
of a finite real random vector has finite second moment, then the covariance matrix
`covarianceMatrix μ X` is positive semidefinite. -/
theorem covarianceMatrix_posSemidef
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n}
    (hX : ∀ i, MeasureTheory.MemLp (fun ω ↦ X ω i) 2 μ) :
    Matrix.PosSemidef (covarianceMatrix μ X) := by
  refine ⟨?_, ?_⟩
  · -- On `ℝ`, symmetry is exactly the Hermitian side of positive semidefiniteness.
    simpa using covarianceMatrix_isSymm (μ := μ) (X := X)
  · intro x
    -- Test the quadratic form against an arbitrary finitely supported coefficient vector.
    have hLx :
        MeasureTheory.MemLp (∑ i ∈ x.support, fun ω ↦ x i * X ω i) 2 μ :=
      coordinateLinearCombination_memLp (μ := μ) (X := X) hX x
    -- Identify the matrix quadratic form with the variance of the scalarized random variable.
    rw [covarianceMatrixQuadraticForm_eq_covariance (μ := μ) (X := X) hX x]
    exact selfCovariance_nonneg_of_memLp hLx

end

/-- The covariance matrix of a zero finite real random vector is the zero matrix. -/
theorem covarianceMatrix_zero {Ω : Type u} [MeasurableSpace Ω] {n : Type v} [Finite n]
    {μ : MeasureTheory.Measure Ω} :
    covarianceMatrix μ (fun _ : Ω ↦ (0 : EuclideanSpace ℝ n)) = 0 := by
  -- Local instance justification (proof-local temporary datum): `covarianceMatrix_apply` and
  -- matrix extensionality require a `Fintype` index, while the theorem itself only uses
  -- finite-dimensional coordinates.
  let _ := Fintype.ofFinite n
  ext i j
  rw [covarianceMatrix_apply]
  simp [covariance]

/-- The covariance matrix of a zero finite real random vector is not positive definite. -/
theorem covarianceMatrix_zero_not_posDef
    {Ω : Type u} [MeasurableSpace Ω] {n : Type v} [Finite n] [Nonempty n]
    {μ : MeasureTheory.Measure Ω} :
    ¬ Matrix.PosDef (covarianceMatrix μ (fun _ : Ω ↦ (0 : EuclideanSpace ℝ n))) := by
  -- Local instance justification (proof-local temporary datum): `Matrix.PosDef.diag_pos` and the
  -- specialization of `covarianceMatrix_zero` use a `Fintype` index, but the statement only
  -- needs finiteness of the coordinate type.
  let _ := Fintype.ofFinite n
  intro h_posDef
  obtain ⟨i⟩ := ‹Nonempty n›
  have h_diag : 0 < covarianceMatrix μ (fun _ : Ω ↦ (0 : EuclideanSpace ℝ n)) i i :=
    Matrix.PosDef.diag_pos h_posDef
  simp [covarianceMatrix_zero] at h_diag

/-- The covariance matrix of the zero random vector on the one-point space is the zero matrix. -/
theorem covarianceMatrix_zeroVector_eq_zero :
    covarianceMatrix (MeasureTheory.Measure.dirac ())
      (fun _ : Unit ↦ (0 : EuclideanSpace ℝ (Fin 1))) = 0 := by
  simpa using
    (covarianceMatrix_zero :
      covarianceMatrix (MeasureTheory.Measure.dirac ())
        (fun _ : Unit ↦ (0 : EuclideanSpace ℝ (Fin 1))) = 0)

/-- exercise_4_1 (3). Exercise 4.1. The covariance matrix of the zero random vector
on the one-point probability space is not positive definite. -/
theorem covarianceMatrix_zeroVector_not_posDef :
    ¬ Matrix.PosDef (covarianceMatrix (MeasureTheory.Measure.dirac ())
      (fun _ : Unit ↦ (0 : EuclideanSpace ℝ (Fin 1)))) := by
  simpa using
    (covarianceMatrix_zero_not_posDef :
      ¬ Matrix.PosDef (covarianceMatrix (MeasureTheory.Measure.dirac ())
        (fun _ : Unit ↦ (0 : EuclideanSpace ℝ (Fin 1)))))

/-- Combined summary for Exercise 4.1: for a finite real random vector with finite second moments
in each coordinate, the covariance matrix `covarianceMatrix μ X` is symmetric and positive
semidefinite, and the zero random vector on the one-point probability space gives a concrete
covariance matrix that is not positive definite. -/
theorem exercise_4_1
    {Ω : Type u} [MeasurableSpace Ω] {n : Type v} [Finite n]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n}
    (hX : ∀ i, MeasureTheory.MemLp (fun ω ↦ X ω i) 2 μ) :
    Matrix.IsSymm (covarianceMatrix μ X) ∧
      Matrix.PosSemidef (covarianceMatrix μ X) ∧
      ¬ Matrix.PosDef (covarianceMatrix (MeasureTheory.Measure.dirac ())
        (fun _ : Unit ↦ (0 : EuclideanSpace ℝ (Fin 1)))) := by
  refine ⟨covarianceMatrix_isSymm (μ := μ) (X := X), ?_, ?_⟩
  · exact covarianceMatrix_posSemidef (μ := μ) (X := X) hX
  · exact covarianceMatrix_zeroVector_not_posDef

end ProbabilityTheory
