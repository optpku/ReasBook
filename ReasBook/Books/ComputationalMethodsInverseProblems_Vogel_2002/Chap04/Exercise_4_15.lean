/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_12
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Exercise_4_15.MinimumVarianceLinear
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Prop_4_35

public section

noncomputable section

namespace ProbabilityTheory

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Fintype n]
variable {m : Type w} [Fintype m] [DecidableEq m]

namespace covarianceFormulaEstimator

/-- Helper for Exercise 4.15: the covariance-form estimator is an affine estimator with matrix
part `crossCovarianceMatrix μ X Z * (covarianceMatrix μ Z)⁻¹` and the unique offset that centers
the observations. -/
theorem covarianceFormulaEstimator_eq_affineEstimator
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {Z : Ω → EuclideanSpace ℝ m} :
    covarianceFormulaEstimator μ X Z =
      affineEstimator
        (crossCovarianceMatrix μ X Z * (covarianceMatrix μ Z)⁻¹)
        (μ[X] - (crossCovarianceMatrix μ X Z * (covarianceMatrix μ Z)⁻¹).toEuclideanLin μ[Z])
        Z := by
  -- Rewrite the centered covariance formula as an offset plus a linear response in `Z`.
  funext ω
  rw [covarianceFormulaEstimator_apply, affineEstimator_apply]
  rw [map_sub]
  simp [sub_eq_add_neg, add_left_comm, add_comm]

/-- Helper for Exercise 4.15: centering both random vectors turns the cross-correlation matrix
into the cross-covariance matrix. -/
theorem crossCorrelationMatrix_centered_eq_crossCovarianceMatrix
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {Z : Ω → EuclideanSpace ℝ m}
    (hX : MeasureTheory.MemLp X 2 μ) (hZ : MeasureTheory.MemLp Z 2 μ) :
    crossCorrelationMatrix μ (X - fun _ ↦ μ[X]) (Z - fun _ ↦ μ[Z]) =
      crossCovarianceMatrix μ X Z := by
  -- Compare the matrix entries and rewrite the coordinate means via `mean_apply`.
  have hX_int : MeasureTheory.Integrable X μ := hX.integrable (by norm_num)
  have hZ_int : MeasureTheory.Integrable Z μ := hZ.integrable (by norm_num)
  ext i j
  rw [crossCorrelationMatrix_apply, crossCovarianceMatrix_apply, ProbabilityTheory.covariance]
  simp [← mean_apply hX_int i, ← mean_apply hZ_int j]

/-- Helper for Exercise 4.15: the centered second-moment matrix is the covariance matrix. -/
theorem secondMomentMatrix_centered_eq_covarianceMatrix
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {Z : Ω → EuclideanSpace ℝ m} (hZ : MeasureTheory.MemLp Z 2 μ) :
    secondMomentMatrix μ (Z - fun _ ↦ μ[Z]) = covarianceMatrix μ Z := by
  -- Compare the matrix entries and rewrite the coordinate means via `mean_apply`.
  have hZ_int : MeasureTheory.Integrable Z μ := hZ.integrable (by norm_num)
  ext i j
  rw [secondMomentMatrix_apply, covarianceMatrix_apply, ProbabilityTheory.covariance]
  simp [← mean_apply hZ_int i, ← mean_apply hZ_int j]

/-- Helper for Exercise 4.15: the affine prediction error is the centered linear residual plus
the deterministic bias term. -/
theorem affineError_eq_centeredResidual_add_bias
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {Z : Ω → EuclideanSpace ℝ m}
    (A : Matrix n m ℝ) (b : EuclideanSpace ℝ n) (ω : Ω) :
    affineEstimator A b Z ω - X ω =
      (linearEstimator A (fun ω ↦ Z ω - μ[Z]) ω - (fun ω ↦ X ω - μ[X]) ω) +
        (b + A.toEuclideanLin μ[Z] - μ[X]) := by
  -- Route correction: normalize the affine error once, then keep later proofs in the centered
  -- linear spelling instead of repeatedly unfolding wrappers.
  rw [affineEstimator_apply, linearEstimator_apply]
  rw [map_sub]
  simp only [sub_eq_add_neg]
  abel_nf

/-- Helper for Exercise 4.15: the centered residual of an affine estimator has zero mean. -/
theorem centeredResidual_mean_zero
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {Z : Ω → EuclideanSpace ℝ m}
    (hX : MeasureTheory.MemLp X 2 μ) (hZ : MeasureTheory.MemLp Z 2 μ)
    (A : Matrix n m ℝ) :
    μ[fun ω ↦ A.toEuclideanLin (Z ω - μ[Z]) - (X ω - μ[X])] = 0 := by
  let Xc : Ω → EuclideanSpace ℝ n := X - fun _ ↦ μ[X]
  let Zc : Ω → EuclideanSpace ℝ m := Z - fun _ ↦ μ[Z]
  have hX_int : MeasureTheory.Integrable X μ := hX.integrable (by norm_num)
  have hZ_int : MeasureTheory.Integrable Z μ := hZ.integrable (by norm_num)
  have hXc : MeasureTheory.MemLp Xc 2 μ := by
    simpa [Xc] using hX.sub (MeasureTheory.memLp_const _)
  have hZc : MeasureTheory.MemLp Zc 2 μ := by
    simpa [Zc] using hZ.sub (MeasureTheory.memLp_const _)
  have hXc_int : MeasureTheory.Integrable Xc μ := hXc.integrable (by norm_num)
  have hZc_int : MeasureTheory.Integrable Zc μ := hZc.integrable (by norm_num)
  have hAZc_int : MeasureTheory.Integrable (fun ω ↦ A.toEuclideanLin (Zc ω)) μ := by
    simpa using
      (hZc.continuousLinearMap_comp A.toEuclideanLin.toContinuousLinearMap).integrable (by norm_num)
  have hXc_zero : μ[Xc] = 0 := by
    simp [Xc, MeasureTheory.integral_sub, hX_int]
  have hZc_zero : μ[Zc] = 0 := by
    simp [Zc, MeasureTheory.integral_sub, hZ_int]
  -- First integrate the centered residual termwise and commute the linear map past the integral.
  change μ[fun ω ↦ A.toEuclideanLin (Zc ω) - Xc ω] = 0
  rw [MeasureTheory.integral_sub hAZc_int hXc_int]
  rw [show μ[fun ω ↦ A.toEuclideanLin (Zc ω)] = A.toEuclideanLin μ[Zc] by
    simpa using ContinuousLinearMap.integral_comp_comm A.toEuclideanLin.toContinuousLinearMap hZc_int]
  -- Each centered mean vanishes because `μ` is a probability measure.
  rw [hZc_zero, hXc_zero]
  simp

/-- Helper for Exercise 4.15: the affine mean-squared error splits into the centered linear
objective plus a deterministic bias penalty. -/
theorem minimumVarianceLinearObjective_affineEstimator_eq_centeredCoefficientObjective_add_bias
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {Z : Ω → EuclideanSpace ℝ m}
    (hX : MeasureTheory.MemLp X 2 μ) (hZ : MeasureTheory.MemLp Z 2 μ)
    (A : Matrix n m ℝ) (b : EuclideanSpace ℝ n) :
    minimumVarianceLinearObjective μ X (affineEstimator A b Z) =
      ProbabilityTheory.MinimumVarianceLinear.coefficientObjective μ
        (fun ω ↦ X ω - μ[X]) (fun ω ↦ Z ω - μ[Z]) A +
      ‖b + A.toEuclideanLin μ[Z] - μ[X]‖ ^ 2 := by
  let Xc : Ω → EuclideanSpace ℝ n := X - fun _ ↦ μ[X]
  let Zc : Ω → EuclideanSpace ℝ m := Z - fun _ ↦ μ[Z]
  let residual : Ω → EuclideanSpace ℝ n := linearEstimator A Zc - Xc
  let bias : EuclideanSpace ℝ n := b + A.toEuclideanLin μ[Z] - μ[X]
  let cross : Ω → ℝ := fun ω ↦ 2 * inner ℝ bias (residual ω)
  let constBias : Ω → ℝ := fun _ ↦ ‖bias‖ ^ 2
  have hZc : MeasureTheory.MemLp Zc 2 μ := by
    simpa [Zc] using hZ.sub (MeasureTheory.memLp_const _)
  have hXc : MeasureTheory.MemLp Xc 2 μ := by
    simpa [Xc] using hX.sub (MeasureTheory.memLp_const _)
  have hResidualLp : MeasureTheory.MemLp residual 2 μ := by
    -- The centered residual is a difference of two square-integrable terms.
    have hLinear :
        MeasureTheory.MemLp (fun ω ↦ A.toEuclideanLin (Zc ω)) 2 μ := by
      simpa using hZc.continuousLinearMap_comp A.toEuclideanLin.toContinuousLinearMap
    have hLinearEq : linearEstimator A Zc = fun ω ↦ A.toEuclideanLin (Zc ω) := by
      funext ω
      rw [linearEstimator_apply]
    have hLinearLp : MeasureTheory.MemLp (linearEstimator A Zc) 2 μ := by
      rw [hLinearEq]
      exact hLinear
    simpa [residual] using hLinearLp.sub hXc
  have hResidualInt : MeasureTheory.Integrable residual μ := hResidualLp.integrable (by norm_num)
  have hResidualSqInt : MeasureTheory.Integrable (fun ω ↦ ‖residual ω‖ ^ 2) μ := by
    exact MeasureTheory.MemLp.integrable_norm_pow (p := 2) hResidualLp (by decide)
  have hCrossInt : MeasureTheory.Integrable cross μ := by
    simpa [cross, bias] using (hResidualInt.const_inner bias).const_mul (2 : ℝ)
  have hBiasInt : MeasureTheory.Integrable constBias μ :=
    MeasureTheory.integrable_const _
  have hResidualMeanZero : μ[residual] = 0 := by
    have hResidualEq : residual = fun ω ↦ A.toEuclideanLin (Zc ω) - Xc ω := by
      funext ω
      simp [residual, linearEstimator_apply]
    rw [hResidualEq]
    simpa [Xc, Zc] using centeredResidual_mean_zero hX hZ A
  have hCrossZero : μ[cross] = 0 := by
    -- The cross term vanishes because the centered residual has mean zero.
    change ∫ x, 2 * inner ℝ bias (residual x) ∂μ = 0
    rw [MeasureTheory.integral_const_mul]
    rw [integral_inner hResidualInt]
    rw [hResidualMeanZero]
    simp
  -- Route correction: after the affine-error normalization, the rest is a direct integral split.
  rw [minimumVarianceLinearObjective_def, ProbabilityTheory.MinimumVarianceLinear.coefficientObjective_def]
  have hResidualEq :
      ∀ ω, linearEstimator A (fun ω ↦ Z ω - μ[Z]) ω - (X ω - μ[X]) = residual ω := by
    intro ω
    simp [residual, Xc, Zc, linearEstimator_apply]
  have hPointwise :
      (fun ω ↦ ‖affineEstimator A b Z ω - X ω‖ ^ 2) = fun ω ↦ ‖residual ω + bias‖ ^ 2 := by
    funext ω
    rw [affineError_eq_centeredResidual_add_bias (μ := μ) (X := X) (Z := Z) A b ω]
    rw [hResidualEq ω]
  rw [hPointwise]
  have hExpand :
      (fun ω ↦ ‖residual ω + bias‖ ^ 2) =
        fun ω ↦ ‖residual ω‖ ^ 2 + cross ω + constBias ω := by
    funext ω
    simp [cross, constBias, norm_add_sq_real, real_inner_comm]
  rw [hExpand]
  have hAssoc :
      (fun ω ↦ ‖residual ω‖ ^ 2 + cross ω + constBias ω) =
        fun ω ↦ ‖residual ω‖ ^ 2 + (cross ω + constBias ω) := by
    funext ω
    ring
  rw [hAssoc]
  have hSplit :
      μ[fun ω ↦ ‖residual ω‖ ^ 2 + (cross ω + constBias ω)] =
        μ[fun ω ↦ ‖residual ω‖ ^ 2] + μ[cross + constBias] := by
    simpa using
      (MeasureTheory.integral_add (μ := μ) (f := fun ω ↦ ‖residual ω‖ ^ 2)
        (g := cross + constBias) hResidualSqInt (hCrossInt.add hBiasInt))
  rw [hSplit]
  have hCrossSplit : μ[cross + constBias] = μ[cross] + μ[constBias] := by
    simpa using
      (MeasureTheory.integral_add (μ := μ) (f := cross) (g := constBias) hCrossInt hBiasInt)
  rw [hCrossSplit, hCrossZero, MeasureTheory.integral_const]
  have hResidualSqEq :
      μ[fun ω ↦ ‖residual ω‖ ^ 2] =
        μ[fun ω ↦ ‖linearEstimator A (fun ω ↦ Z ω - μ[Z]) ω - (X ω - μ[X])‖ ^ 2] := by
    exact congrArg (fun f : Ω → EuclideanSpace ℝ n ↦ μ[fun ω ↦ ‖f ω‖ ^ 2])
      (funext fun ω ↦ (hResidualEq ω).symm)
  rw [hResidualSqEq]
  simp [bias]

/-- Helper for Exercise 4.15: affine estimators of square-integrable observations remain
square-integrable. -/
theorem memLp_affineEstimator_of_memLp
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {Z : Ω → EuclideanSpace ℝ m} (hZ : MeasureTheory.MemLp Z 2 μ)
    (A : Matrix n m ℝ) (b : EuclideanSpace ℝ n) :
    MeasureTheory.MemLp (affineEstimator A b Z) 2 μ := by
  -- Split the affine estimator into a constant term and a linear term.
  have hLinear : MeasureTheory.MemLp (fun ω ↦ A.toEuclideanLin (Z ω)) 2 μ := by
    simpa using hZ.continuousLinearMap_comp A.toEuclideanLin.toContinuousLinearMap
  have hAffineEq : affineEstimator A b Z = (fun _ ↦ b) + fun ω ↦ A.toEuclideanLin (Z ω) := by
    funext ω
    simp [affineEstimator_apply]
  rw [hAffineEq]
  exact (MeasureTheory.memLp_const b).add hLinear

/-- Helper for Exercise 4.15: an optimal centered coefficient yields an optimal affine
estimator on the admissible affine class. -/
theorem affineEstimator_isMinOn_of_isOptimalCoefficient_centered
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {Z : Ω → EuclideanSpace ℝ m}
    (hX : MeasureTheory.MemLp X 2 μ) (hZ : MeasureTheory.MemLp Z 2 μ)
    {A : Matrix n m ℝ}
    (hA : ProbabilityTheory.MinimumVarianceLinear.IsOptimalCoefficient μ
      (fun ω ↦ X ω - μ[X]) (fun ω ↦ Z ω - μ[Z]) A) :
    IsMinOn (minimumVarianceLinearObjective μ X) (minimumVarianceLinearAdmissibleSet μ Z)
      (affineEstimator A (μ[X] - A.toEuclideanLin μ[Z]) Z) := by
  have hAmin :
      ∀ B : Matrix n m ℝ,
        ProbabilityTheory.MinimumVarianceLinear.coefficientObjective μ
            (fun ω ↦ X ω - μ[X]) (fun ω ↦ Z ω - μ[Z]) A ≤
          ProbabilityTheory.MinimumVarianceLinear.coefficientObjective μ
            (fun ω ↦ X ω - μ[X]) (fun ω ↦ Z ω - μ[Z]) B := by
    simpa [IsMinOn, IsMinFilter, Filter.eventually_top] using hA.isMinOn
  -- Compare against an arbitrary admissible affine competitor and bound its bias penalty by `0 ≤ _`.
  change
    ∀ Y,
      minimumVarianceLinearAdmissibleSet μ Z Y →
        minimumVarianceLinearObjective μ X
            (affineEstimator A (μ[X] - A.toEuclideanLin μ[Z]) Z) ≤
          minimumVarianceLinearObjective μ X Y
  intro Y hY
  change Y ∈ minimumVarianceLinearAdmissibleSet μ Z at hY
  rw [mem_minimumVarianceLinearAdmissibleSet_iff] at hY
  rcases hY with ⟨B, b, rfl, _hMemY⟩
  have hCoeffLe :
      ProbabilityTheory.MinimumVarianceLinear.coefficientObjective μ
          (fun ω ↦ X ω - μ[X]) (fun ω ↦ Z ω - μ[Z]) A ≤
        ProbabilityTheory.MinimumVarianceLinear.coefficientObjective μ
          (fun ω ↦ X ω - μ[X]) (fun ω ↦ Z ω - μ[Z]) B :=
    hAmin B
  have hBiasNonneg : 0 ≤ ‖b + B.toEuclideanLin μ[Z] - μ[X]‖ ^ 2 := sq_nonneg _
  calc
    minimumVarianceLinearObjective μ X
        (affineEstimator A (μ[X] - A.toEuclideanLin μ[Z]) Z)
      =
        ProbabilityTheory.MinimumVarianceLinear.coefficientObjective μ
            (fun ω ↦ X ω - μ[X]) (fun ω ↦ Z ω - μ[Z]) A := by
          rw [minimumVarianceLinearObjective_affineEstimator_eq_centeredCoefficientObjective_add_bias
            hX hZ]
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ ≤
        ProbabilityTheory.MinimumVarianceLinear.coefficientObjective μ
          (fun ω ↦ X ω - μ[X]) (fun ω ↦ Z ω - μ[Z]) B := hCoeffLe
    _ ≤
        ProbabilityTheory.MinimumVarianceLinear.coefficientObjective μ
          (fun ω ↦ X ω - μ[X]) (fun ω ↦ Z ω - μ[Z]) B +
            ‖b + B.toEuclideanLin μ[Z] - μ[X]‖ ^ 2 := by
          linarith
    _ = minimumVarianceLinearObjective μ X (affineEstimator B b Z) := by
          rw [minimumVarianceLinearObjective_affineEstimator_eq_centeredCoefficientObjective_add_bias
            hX hZ]

/-- Exercise 4.15. Proposition 4.35 states that the centered affine covariance formula
`covarianceFormulaEstimator μ X Z` is a minimum-variance linear estimator of `X` from `Z` when
`covarianceMatrix μ Z` is nonsingular. -/
theorem isMinimumVarianceLinearEstimator
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {Z : Ω → EuclideanSpace ℝ m}
    (hX : MeasureTheory.MemLp X 2 μ) (hZ : MeasureTheory.MemLp Z 2 μ)
    (h_covZ : IsUnit (covarianceMatrix μ Z).det) :
    IsMinimumVarianceLinearEstimator μ X Z (covarianceFormulaEstimator μ X Z) := by
  let Xc : Ω → EuclideanSpace ℝ n := X - fun _ ↦ μ[X]
  let Zc : Ω → EuclideanSpace ℝ m := Z - fun _ ↦ μ[Z]
  let A : Matrix n m ℝ := crossCovarianceMatrix μ X Z * (covarianceMatrix μ Z)⁻¹
  have hXc : MeasureTheory.MemLp Xc 2 μ := by
    simpa [Xc] using hX.sub (MeasureTheory.memLp_const _)
  have hZc : MeasureTheory.MemLp Zc 2 μ := by
    simpa [Zc] using hZ.sub (MeasureTheory.memLp_const _)
  have hCross :
      crossCorrelationMatrix μ Xc Zc = crossCovarianceMatrix μ X Z := by
    simpa [Xc, Zc] using crossCorrelationMatrix_centered_eq_crossCovarianceMatrix hX hZ
  have hSecond : secondMomentMatrix μ Zc = covarianceMatrix μ Z := by
    simpa [Zc] using secondMomentMatrix_centered_eq_covarianceMatrix hZ
  have hSecondUnit : IsUnit (secondMomentMatrix μ Zc).det := by
    simpa [hSecond] using h_covZ
  -- Apply Proposition 4.35 to the centered random vectors and rewrite the resulting matrix.
  have hA :
      ProbabilityTheory.MinimumVarianceLinear.IsOptimalCoefficient μ Xc Zc A := by
    simpa [A, hCross, hSecond] using
      (ProbabilityTheory.MinimumVarianceLinear.isOptimalCoefficient_crossCorrelationFormula
        (μ := μ) (X := Xc) (Z := Zc) hXc hZc hSecondUnit)
  -- Package admissibility separately so the `IsMinOn` transfer stays purely order-theoretic.
  have hMem :
      affineEstimator A (μ[X] - A.toEuclideanLin μ[Z]) Z ∈ minimumVarianceLinearAdmissibleSet μ Z := by
    rw [mem_minimumVarianceLinearAdmissibleSet_iff]
    exact ⟨A, μ[X] - A.toEuclideanLin μ[Z], rfl,
      memLp_affineEstimator_of_memLp hZ A (μ[X] - A.toEuclideanLin μ[Z])⟩
  -- Transfer the centered coefficient minimizer to the affine admissible class via the bias split.
  have hOpt :
      IsMinOn (minimumVarianceLinearObjective μ X) (minimumVarianceLinearAdmissibleSet μ Z)
        (affineEstimator A (μ[X] - A.toEuclideanLin μ[Z]) Z) := by
    exact affineEstimator_isMinOn_of_isOptimalCoefficient_centered hX hZ hA
  -- Finish by rewriting the covariance formula into the canonical affine normal form.
  rw [covarianceFormulaEstimator_eq_affineEstimator]
  exact IsMinimumVarianceLinearEstimator.ofMemOptimal μ X Z _ hMem hOpt

/-- The covariance-form estimator belongs to
`minimumVarianceLinearAdmissibleSet μ Z` under the hypotheses of Exercise 4.15. -/
theorem mem_admissible
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {Z : Ω → EuclideanSpace ℝ m}
    (hX : MeasureTheory.MemLp X 2 μ) (hZ : MeasureTheory.MemLp Z 2 μ)
    (h_covZ : IsUnit (covarianceMatrix μ Z).det) :
    covarianceFormulaEstimator μ X Z ∈ minimumVarianceLinearAdmissibleSet μ Z :=
  (isMinimumVarianceLinearEstimator hX hZ h_covZ).mem_admissible

/-- The covariance-form estimator minimizes `minimumVarianceLinearObjective μ X` on
`minimumVarianceLinearAdmissibleSet μ Z` under the hypotheses of Exercise 4.15. -/
theorem optimal
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {Z : Ω → EuclideanSpace ℝ m}
    (hX : MeasureTheory.MemLp X 2 μ) (hZ : MeasureTheory.MemLp Z 2 μ)
    (h_covZ : IsUnit (covarianceMatrix μ Z).det) :
    IsMinOn (minimumVarianceLinearObjective μ X) (minimumVarianceLinearAdmissibleSet μ Z)
      (covarianceFormulaEstimator μ X Z) :=
  (isMinimumVarianceLinearEstimator hX hZ h_covZ).optimal

end covarianceFormulaEstimator

end

end ProbabilityTheory
