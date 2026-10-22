/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_27.CrossCorrelation
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_34.MinimumVarianceLinear
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Prop_4_29
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

noncomputable section

open scoped Matrix

namespace ProbabilityTheory
namespace MinimumVarianceLinear

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Fintype n]
variable {m : Type w} [Fintype m] [DecidableEq m]

/-- Helper for Proposition 4.35: cross-correlation against a linear estimator is right
multiplication by the transposed coefficient matrix. -/
lemma crossCorrelationMatrix_linearEstimator_right
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {p : Type*} [Fintype p]
    {X : Ω → EuclideanSpace ℝ p} {Z : Ω → EuclideanSpace ℝ m}
    (hX : MeasureTheory.MemLp X 2 μ) (hZ : MeasureTheory.MemLp Z 2 μ)
    (B : Matrix n m ℝ) :
    crossCorrelationMatrix μ X (linearEstimator B Z) =
      crossCorrelationMatrix μ X Z * Bᵀ := by
  have hXcoord : ∀ i, MeasureTheory.MemLp (fun ω ↦ X ω i) 2 μ :=
    MeasureTheory.memLp_piLp_iff.mp hX
  have hZcoord : ∀ j, MeasureTheory.MemLp (fun ω ↦ Z ω j) 2 μ :=
    MeasureTheory.memLp_piLp_iff.mp hZ
  ext i j
  rw [crossCorrelationMatrix_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  -- Expand the `j`th coordinate of the linear estimator into a finite linear combination.
  have hPointwise :
      (fun ω ↦ X ω i * (linearEstimator B Z ω) j) =
        fun ω ↦ ∑ k, B j k * (X ω i * Z ω k) := by
    funext ω
    rw [linearEstimator_apply]
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]
  rw [hPointwise]
  -- Move the finite sum and constant coefficients through the integral coordinatewise.
  rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
    (f := fun k ω ↦ B j k * (X ω i * Z ω k))
    (fun k _ ↦ ((hXcoord i).integrable_mul (hZcoord k)).const_mul _)]
  simp_rw [MeasureTheory.integral_const_mul]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [crossCorrelationMatrix_apply]
  ring

/-- Helper for Proposition 4.35: the second moment of a linear estimator is the pushed-forward
quadratic form `B * secondMomentMatrix μ Z * Bᵀ`. -/
lemma secondMomentMatrix_linearEstimator
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {Z : Ω → EuclideanSpace ℝ m}
    (hZ : MeasureTheory.MemLp Z 2 μ) (B : Matrix n m ℝ) :
    secondMomentMatrix μ (linearEstimator B Z) =
      B * secondMomentMatrix μ Z * Bᵀ := by
  have hLinear : MeasureTheory.MemLp (linearEstimator B Z) 2 μ := by
    have hLinearEq : linearEstimator B Z = fun ω ↦ B.toEuclideanLin (Z ω) := by
      funext ω
      rw [linearEstimator_apply]
    rw [hLinearEq]
    exact hZ.continuousLinearMap_comp B.toEuclideanLin.toContinuousLinearMap
  have hLeft :
      crossCorrelationMatrix μ (linearEstimator B Z) Z = B * secondMomentMatrix μ Z := by
    -- Route correction: compute the left factor via transpose rather than unfolding the whole
    -- second-moment matrix in place.
    rw [crossCorrelationMatrix_transpose, crossCorrelationMatrix_linearEstimator_right hZ hZ B]
    simp [Matrix.transpose_mul, secondMomentMatrix_transpose, crossCorrelationMatrix_self]
  -- Rewrite the square self cross-correlation through the right-action lemma.
  calc
    secondMomentMatrix μ (linearEstimator B Z)
        = crossCorrelationMatrix μ (linearEstimator B Z) (linearEstimator B Z) := by
            rw [← crossCorrelationMatrix_self]
    _ = crossCorrelationMatrix μ (linearEstimator B Z) Z * Bᵀ := by
          rw [crossCorrelationMatrix_linearEstimator_right hLinear hZ B]
    _ = B * secondMomentMatrix μ Z * Bᵀ := by
          rw [hLeft]

/-- Helper for Proposition 4.35: the second moment of a difference expands into the expected
quadratic and mixed cross-correlation terms. -/
lemma secondMomentMatrix_sub
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {Y X : Ω → EuclideanSpace ℝ n}
    (hY : MeasureTheory.MemLp Y 2 μ) (hX : MeasureTheory.MemLp X 2 μ) :
    secondMomentMatrix μ (fun ω ↦ Y ω - X ω) =
      secondMomentMatrix μ Y - crossCorrelationMatrix μ Y X -
        crossCorrelationMatrix μ X Y + secondMomentMatrix μ X := by
  have hYcoord : ∀ i, MeasureTheory.MemLp (fun ω ↦ Y ω i) 2 μ :=
    MeasureTheory.memLp_piLp_iff.mp hY
  have hXcoord : ∀ i, MeasureTheory.MemLp (fun ω ↦ X ω i) 2 μ :=
    MeasureTheory.memLp_piLp_iff.mp hX
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, secondMomentMatrix_apply,
    crossCorrelationMatrix_apply]
  have hYY : MeasureTheory.Integrable (fun ω ↦ Y ω i * Y ω j) μ :=
    (hYcoord i).integrable_mul (hYcoord j)
  have hYX : MeasureTheory.Integrable (fun ω ↦ Y ω i * X ω j) μ :=
    (hYcoord i).integrable_mul (hXcoord j)
  have hXY : MeasureTheory.Integrable (fun ω ↦ X ω i * Y ω j) μ :=
    (hXcoord i).integrable_mul (hYcoord j)
  have hXX : MeasureTheory.Integrable (fun ω ↦ X ω i * X ω j) μ :=
    (hXcoord i).integrable_mul (hXcoord j)
  have hExpand :
      (fun ω ↦ (Y ω i - X ω i) * (Y ω j - X ω j)) =
        fun ω ↦ (Y ω i * Y ω j - Y ω i * X ω j) - (X ω i * Y ω j - X ω i * X ω j) := by
    funext ω
    ring
  -- Expand the integrand algebraically and then split the integral termwise.
  change ∫ ω, (Y ω i - X ω i) * (Y ω j - X ω j) ∂μ = _
  rw [hExpand]
  have hSplit :
      ∫ ω, Y ω i * Y ω j - Y ω i * X ω j - (X ω i * Y ω j - X ω i * X ω j) ∂μ =
        (∫ ω, Y ω i * Y ω j - Y ω i * X ω j ∂μ) -
          ∫ ω, X ω i * Y ω j - X ω i * X ω j ∂μ := by
    simpa using
      (MeasureTheory.integral_sub (μ := μ)
        (f := fun ω ↦ Y ω i * Y ω j - Y ω i * X ω j)
        (g := fun ω ↦ X ω i * Y ω j - X ω i * X ω j)
        (hYY.sub hYX) (hXY.sub hXX))
  have hSplitLeft :
      ∫ ω, Y ω i * Y ω j - Y ω i * X ω j ∂μ =
        (∫ ω, Y ω i * Y ω j ∂μ) - ∫ ω, Y ω i * X ω j ∂μ := by
    simpa using
      (MeasureTheory.integral_sub (μ := μ)
        (f := fun ω ↦ Y ω i * Y ω j) (g := fun ω ↦ Y ω i * X ω j) hYY hYX)
  have hSplitRight :
      ∫ ω, X ω i * Y ω j - X ω i * X ω j ∂μ =
        (∫ ω, X ω i * Y ω j ∂μ) - ∫ ω, X ω i * X ω j ∂μ := by
    simpa using
      (MeasureTheory.integral_sub (μ := μ)
        (f := fun ω ↦ X ω i * Y ω j) (g := fun ω ↦ X ω i * X ω j) hXY hXX)
  calc
    ∫ ω, Y ω i * Y ω j - Y ω i * X ω j - (X ω i * Y ω j - X ω i * X ω j) ∂μ
        = (∫ ω, Y ω i * Y ω j - Y ω i * X ω j ∂μ) -
          ∫ ω, X ω i * Y ω j - X ω i * X ω j ∂μ := hSplit
    _ = ((∫ ω, Y ω i * Y ω j ∂μ) - ∫ ω, Y ω i * X ω j ∂μ) -
          ((∫ ω, X ω i * Y ω j ∂μ) - ∫ ω, X ω i * X ω j ∂μ) := by
            rw [hSplitLeft, hSplitRight]
    _ = _ := by
          ring

/-- Helper for Proposition 4.35: the mean-squared coefficient objective is a quadratic trace
expression in the coefficient matrix. -/
lemma coefficientObjective_eq_trace_quadratic
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {Z : Ω → EuclideanSpace ℝ m}
    (hX : MeasureTheory.MemLp X 2 μ) (hZ : MeasureTheory.MemLp Z 2 μ)
    (B : Matrix n m ℝ) :
    coefficientObjective μ X Z B =
      Matrix.trace (B * secondMomentMatrix μ Z * Bᵀ) -
        2 * Matrix.trace (B * (crossCorrelationMatrix μ X Z)ᵀ) +
        Matrix.trace (secondMomentMatrix μ X) := by
  have hLinear : MeasureTheory.MemLp (linearEstimator B Z) 2 μ := by
    have hLinearEq : linearEstimator B Z = fun ω ↦ B.toEuclideanLin (Z ω) := by
      funext ω
      rw [linearEstimator_apply]
    rw [hLinearEq]
    exact hZ.continuousLinearMap_comp B.toEuclideanLin.toContinuousLinearMap
  have hResidual : MeasureTheory.MemLp (fun ω ↦ linearEstimator B Z ω - X ω) 2 μ := by
    change MeasureTheory.MemLp (linearEstimator B Z - X) 2 μ
    exact hLinear.sub hX
  have hCrossRight :
      crossCorrelationMatrix μ X (linearEstimator B Z) =
        crossCorrelationMatrix μ X Z * Bᵀ :=
    crossCorrelationMatrix_linearEstimator_right hX hZ B
  have hCrossLeft :
      crossCorrelationMatrix μ (linearEstimator B Z) X =
        B * (crossCorrelationMatrix μ X Z)ᵀ := by
    -- Normalize the left mixed term by transposing the right mixed term.
    rw [crossCorrelationMatrix_transpose, hCrossRight]
    simp [Matrix.transpose_mul]
  have hTraceCrossRight :
      Matrix.trace (crossCorrelationMatrix μ X (linearEstimator B Z)) =
        Matrix.trace (B * (crossCorrelationMatrix μ X Z)ᵀ) := by
    rw [hCrossRight]
    rw [← Matrix.trace_transpose (crossCorrelationMatrix μ X Z * Bᵀ)]
    simp [Matrix.transpose_mul]
  -- Convert the residual norm into a trace and rewrite the mixed terms through the helpers.
  rw [coefficientObjective_def, ProbabilityTheory.expected_sqNorm_eq_trace_secondMomentMatrix
    hResidual, secondMomentMatrix_sub hLinear hX, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_sub, secondMomentMatrix_linearEstimator hZ B, hCrossLeft, hTraceCrossRight]
  ring

/-- Helper for Proposition 4.35: any coefficient solving the normal equation completes the
quadratic objective around its minimizer candidate. -/
lemma quadraticTrace_completion_of_normalEquation
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {Z : Ω → EuclideanSpace ℝ m}
    (hX : MeasureTheory.MemLp X 2 μ) (hZ : MeasureTheory.MemLp Z 2 μ)
    {B0 : Matrix n m ℝ}
    (hNormal : B0 * secondMomentMatrix μ Z = crossCorrelationMatrix μ X Z)
    (B : Matrix n m ℝ) :
    coefficientObjective μ X Z B =
      coefficientObjective μ X Z B0 +
        Matrix.trace ((B - B0) * secondMomentMatrix μ Z * (B - B0)ᵀ) := by
  have hSecondTranspose :
      (secondMomentMatrix μ Z)ᵀ = secondMomentMatrix μ Z :=
    secondMomentMatrix_transpose (μ := μ) (X := Z)
  have hNormalT :
      (crossCorrelationMatrix μ X Z)ᵀ = secondMomentMatrix μ Z * B0ᵀ := by
    -- Transpose the normal equation to rewrite the mixed term in the quadratic form.
    simpa [Matrix.transpose_mul, hSecondTranspose] using
      (congrArg Matrix.transpose hNormal).symm
  have hTraceSymm :
      Matrix.trace (B0 * secondMomentMatrix μ Z * Bᵀ) =
        Matrix.trace (B * secondMomentMatrix μ Z * B0ᵀ) := by
    -- The two mixed traces agree because they are transposes of one another.
    rw [← Matrix.trace_transpose (B0 * secondMomentMatrix μ Z * Bᵀ)]
    simp [Matrix.transpose_mul, hSecondTranspose, Matrix.mul_assoc]
  have hRemainder :
      Matrix.trace ((B - B0) * secondMomentMatrix μ Z * (B - B0)ᵀ) =
        Matrix.trace (B * secondMomentMatrix μ Z * Bᵀ) -
          Matrix.trace (B * secondMomentMatrix μ Z * B0ᵀ) -
          Matrix.trace (B0 * secondMomentMatrix μ Z * Bᵀ) +
          Matrix.trace (B0 * secondMomentMatrix μ Z * B0ᵀ) := by
    -- Expand the remainder trace after distributing the matrix subtraction on both sides.
    calc
      Matrix.trace ((B - B0) * secondMomentMatrix μ Z * (B - B0)ᵀ)
          = Matrix.trace (((B - B0) * secondMomentMatrix μ Z) * (B - B0)ᵀ) := by
              rw [Matrix.mul_assoc]
      _ = Matrix.trace (((B * secondMomentMatrix μ Z) - (B0 * secondMomentMatrix μ Z)) *
            (Bᵀ - B0ᵀ)) := by
              rw [Matrix.sub_mul, Matrix.transpose_sub]
      _ = Matrix.trace (((B * secondMomentMatrix μ Z) * Bᵀ -
            (B * secondMomentMatrix μ Z) * B0ᵀ) -
            ((B0 * secondMomentMatrix μ Z) * Bᵀ -
              (B0 * secondMomentMatrix μ Z) * B0ᵀ)) := by
              rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
      _ = Matrix.trace ((B * secondMomentMatrix μ Z) * Bᵀ -
            (B * secondMomentMatrix μ Z) * B0ᵀ) -
            Matrix.trace ((B0 * secondMomentMatrix μ Z) * Bᵀ -
              (B0 * secondMomentMatrix μ Z) * B0ᵀ) := by
              rw [Matrix.trace_sub]
      _ = (Matrix.trace ((B * secondMomentMatrix μ Z) * Bᵀ) -
            Matrix.trace ((B * secondMomentMatrix μ Z) * B0ᵀ)) -
            (Matrix.trace ((B0 * secondMomentMatrix μ Z) * Bᵀ) -
              Matrix.trace ((B0 * secondMomentMatrix μ Z) * B0ᵀ)) := by
              rw [Matrix.trace_sub, Matrix.trace_sub]
      _ = _ := by
            ring
  have hCrossB :
      Matrix.trace (B * (crossCorrelationMatrix μ X Z)ᵀ) =
        Matrix.trace (B * secondMomentMatrix μ Z * B0ᵀ) := by
    rw [hNormalT]
    simp [Matrix.mul_assoc]
  have hCrossB0 :
      Matrix.trace (B0 * (crossCorrelationMatrix μ X Z)ᵀ) =
        Matrix.trace (B0 * secondMomentMatrix μ Z * B0ᵀ) := by
    rw [hNormalT]
    simp [Matrix.mul_assoc]
  -- Rewrite both objectives in quadratic trace form and collapse the scalar algebra.
  rw [coefficientObjective_eq_trace_quadratic hX hZ B,
    coefficientObjective_eq_trace_quadratic hX hZ B0, hRemainder, hCrossB, hCrossB0,
    hTraceSymm]
  ring

/-- Proposition 4.35. If `ΓZZ = secondMomentMatrix μ Z` is nonsingular, then the minimum
variance linear estimator of `X` from `Z` is
`linearEstimator (crossCorrelationMatrix μ X Z * (secondMomentMatrix μ Z)⁻¹) Z`. -/
theorem isOptimalCoefficient_crossCorrelationFormula
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {Z : Ω → EuclideanSpace ℝ m}
    (hX : MeasureTheory.MemLp X 2 μ) (hZ : MeasureTheory.MemLp Z 2 μ)
    (h_ΓZZ : IsUnit (secondMomentMatrix μ Z).det) :
    IsOptimalCoefficient μ X Z
      (crossCorrelationMatrix μ X Z * (secondMomentMatrix μ Z)⁻¹) := by
  let B0 := crossCorrelationMatrix μ X Z * (secondMomentMatrix μ Z)⁻¹
  have hNormal : B0 * secondMomentMatrix μ Z = crossCorrelationMatrix μ X Z := by
    -- The candidate coefficient satisfies the normal equation by inverse cancellation.
    simpa [B0, Matrix.mul_assoc] using
      Matrix.nonsing_inv_mul_cancel_right (A := secondMomentMatrix μ Z)
        (B := crossCorrelationMatrix μ X Z) h_ΓZZ
  rw [isOptimalCoefficient_iff]
  refine ⟨?_, ?_⟩
  · rw [hasFiniteSecondMoments_iff]
    exact ⟨hX, hZ⟩
  -- On `Set.univ`, optimality reduces to a pointwise comparison of the coefficient objective.
  simpa [IsMinOn, IsMinFilter, Filter.eventually_top, B0] using
    (show ∀ B : Matrix n m ℝ,
      coefficientObjective μ X Z B0 ≤ coefficientObjective μ X Z B from by
        intro B
        have hLinear : MeasureTheory.MemLp (linearEstimator (B - B0) Z) 2 μ := by
          have hLinearEq :
              linearEstimator (B - B0) Z = fun ω ↦ (B - B0).toEuclideanLin (Z ω) := by
            funext ω
            rw [linearEstimator_apply]
          rw [hLinearEq]
          exact hZ.continuousLinearMap_comp (B - B0).toEuclideanLin.toContinuousLinearMap
        have hNonneg :
            0 ≤ Matrix.trace ((B - B0) * secondMomentMatrix μ Z * (B - B0)ᵀ) := by
          -- Identify the remainder trace with the expected squared norm of the residual factor.
          rw [← secondMomentMatrix_linearEstimator hZ (B - B0)]
          rw [← ProbabilityTheory.expected_sqNorm_eq_trace_secondMomentMatrix hLinear]
          exact MeasureTheory.integral_nonneg fun ω ↦ by positivity
        have hCompletion :=
          quadraticTrace_completion_of_normalEquation (μ := μ) (X := X) (Z := Z)
            hX hZ (B0 := B0) hNormal B
        linarith)

/-- Proposition 4.35. If `ΓZZ = secondMomentMatrix μ Z` is nonsingular, then the minimum
variance linear estimator of `X` from `Z` is
`linearEstimator (crossCorrelationMatrix μ X Z * (secondMomentMatrix μ Z)⁻¹) Z`. -/
theorem isEstimator_crossCorrelationFormula
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {Z : Ω → EuclideanSpace ℝ m}
    (hX : MeasureTheory.MemLp X 2 μ) (hZ : MeasureTheory.MemLp Z 2 μ)
    (h_ΓZZ : IsUnit (secondMomentMatrix μ Z).det) :
    IsEstimator μ X Z
      (linearEstimator (crossCorrelationMatrix μ X Z * (secondMomentMatrix μ Z)⁻¹) Z) := by
  rw [isEstimator_iff]
  exact ⟨crossCorrelationMatrix μ X Z * (secondMomentMatrix μ Z)⁻¹, rfl,
    isOptimalCoefficient_crossCorrelationFormula hX hZ h_ΓZZ⟩

end

end MinimumVarianceLinear
end ProbabilityTheory
