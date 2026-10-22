/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Exercise_11_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Exercise_11_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_5_1
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

local notation "Point" => EuclideanSpace ℝ (Fin 2)
local notation "projectedGradient114" =>
  linearlyConstrainedDirectionSearchObjective chapter11Exercise113Objective

-- Source/core/bridge triage:
-- * source-facing: the scalar first-order and second-order data of the Exercise 11.3 objective
--   along the normalized null direction of the equality constraint.
-- * inspected owners: `linearlyConstrainedDirectionSearchObjective` from `Exercise_11_1`,
--   `hessianQuadraticAt` from `Chapter03.Definition_3_5_1`,
--   `projectedGradientReducedGradient` from `Algorithm_11_4_1`, and
--   `LinearEqualityConstrainedProblem.feasibleSet` from `Lemma_11_5_4`.
-- * core/canonical: `linearlyConstrainedDirectionSearchObjective` for the directional pairing and
--   `hessianQuadraticAt` for the second-order directional evaluation.
-- * bridge/view: the exercise-specific null direction used to evaluate those canonical owners.

/-- The point `(3, -2)ᵀ` requested in Exercise 11.4. -/
def chapter11Exercise114TestPoint : Point :=
  EuclideanSpace.single 0 (3 : ℝ) + EuclideanSpace.single 1 (-2 : ℝ)

/-- The standard normalized null-space direction `z = (1 / √2) * (1, -1)ᵀ` for the constraint
`x 0 + x 1 = 1`. -/
def chapter11Exercise114NullDirection : Point :=
  EuclideanSpace.single 0 (Real.sqrt 2 / 2) +
    EuclideanSpace.single 1 (-(Real.sqrt 2 / 2))

/-- Helper for Chapter11 Exercise 11.4: the `i`-th coordinate projection on `Point` has
gradient `eᵢ`. -/
theorem chapter11Exercise114_hasGradientAtCoordinateProjection (i : Fin 2) (x : Point) :
    HasGradientAt (fun y : Point ↦ y i) (EuclideanSpace.single i (1 : ℝ)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hdual :
      InnerProductSpace.toDual ℝ Point (EuclideanSpace.single i (1 : ℝ)) =
        PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) i := by
    ext v
    -- The Riesz representation of `eᵢ` is evaluation at the `i`-th coordinate.
    simp [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]
  simpa [hdual] using
    (PiLp.hasFDerivAt_apply (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 2 ↦ ℝ) x i)

/-- Helper for Chapter11 Exercise 11.4: the Riesz dual of the scaled basis vector `a • eᵢ`
is the scaled `i`-th coordinate projection. -/
theorem toDual_single_eq_smul_proj (i : Fin 2) (a : ℝ) :
    InnerProductSpace.toDual ℝ Point (EuclideanSpace.single i a) =
      a • PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) i := by
  -- Evaluate both continuous linear maps on an arbitrary vector and compare coordinates.
  ext v
  simp [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]

/-- Helper for Chapter11 Exercise 11.4: the reused quartic objective has the explicit gradient
`(32 x₀^3, -4 x₁^3)`. -/
theorem chapter11Exercise114Objective_hasGradientAt (x : Point) :
    HasGradientAt
      chapter11Exercise113Objective
      (EuclideanSpace.single 0 (32 * x 0 ^ (3 : ℕ)) +
        EuclideanSpace.single 1 (-4 * x 1 ^ (3 : ℕ)))
      x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hcoord0 := (chapter11Exercise114_hasGradientAtCoordinateProjection 0 x).hasFDerivAt
  have hcoord1 := (chapter11Exercise114_hasGradientAtCoordinateProjection 1 x).hasFDerivAt
  -- The objective is the difference of those two scalar pieces.
  let hsum := (((hcoord0.pow 4).const_mul (8 : ℝ)).sub (hcoord1.pow 4))
  refine (hsum.congr_fderiv ?_).congr_of_eventuallyEq ?_
  · ext v
    simp [toDual_single_eq_smul_proj, sub_eq_add_neg, smul_smul, nsmul_eq_mul]
    ring_nf
    simp
  · filter_upwards with y
    simp [chapter11Exercise113Objective, sub_eq_add_neg]

/-- Helper for Chapter11 Exercise 11.4: the gradient of the reused quartic objective is the
explicit vector field `x ↦ (32 x₀^3, -4 x₁^3)`. -/
theorem chapter11Exercise114Objective_gradient_eq (x : Point) :
    gradient chapter11Exercise113Objective x =
      EuclideanSpace.single 0 (32 * x 0 ^ (3 : ℕ)) +
        EuclideanSpace.single 1 (-4 * x 1 ^ (3 : ℕ)) :=
  (chapter11Exercise114Objective_hasGradientAt x).gradient

/-- Helper for Chapter11 Exercise 11.4: along the normalized null-space direction, the projected
gradient simplifies to the scalar polynomial `2 √2 (8 x₀^3 + x₁^3)`. -/
theorem chapter11Exercise114_projectedGradient_nullDirection_eq (x : Point) :
    projectedGradient114 x chapter11Exercise114NullDirection =
      2 * Real.sqrt 2 * (8 * x 0 ^ (3 : ℕ) + x 1 ^ (3 : ℕ)) := by
  -- Expand the directional pairing and then collapse the two-coordinate inner product.
  rw [linearlyConstrainedDirectionSearchObjective_apply, chapter11Exercise114Objective_gradient_eq]
  simp [chapter11Exercise114NullDirection, PiLp.inner_apply, Fin.sum_univ_two, PiLp.single_apply]
  ring_nf

/-- Helper for Chapter11 Exercise 11.4: the explicit cubic gradient field has the diagonal
Fréchet derivative `v ↦ (96 x₀² v₀, -12 x₁² v₁)`. -/
theorem chapter11Exercise114GradientField_hasFDerivAt (x : Point) :
    HasFDerivAt
      (fun y : Point ↦
        EuclideanSpace.single 0 (32 * y 0 ^ (3 : ℕ)) +
          EuclideanSpace.single 1 (-4 * y 1 ^ (3 : ℕ)))
      (((96 * x 0 ^ (2 : ℕ)) •
          ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0) : Point →L[ℝ] ℝ)).smulRight
          ((EuclideanSpace.single 0 (1 : ℝ)) : Point) +
        ((-12 * x 1 ^ (2 : ℕ)) •
            ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1) : Point →L[ℝ] ℝ)).smulRight
          ((EuclideanSpace.single 1 (1 : ℝ)) : Point))
      x := by
  let e0 : Point := EuclideanSpace.single 0 (1 : ℝ)
  let e1 : Point := EuclideanSpace.single 1 (1 : ℝ)
  have hcoord0 := (chapter11Exercise114_hasGradientAtCoordinateProjection 0 x).hasFDerivAt
  have hcoord1 := (chapter11Exercise114_hasGradientAtCoordinateProjection 1 x).hasFDerivAt
  have hscalar0 :
      HasFDerivAt
        (fun y : Point ↦ (32 * y 0 ^ (3 : ℕ)) • e0)
        (((3 * (32 * x 0 ^ (2 : ℕ))) •
            InnerProductSpace.toDual ℝ Point (EuclideanSpace.single 0 (1 : ℝ))).smulRight
          e0)
        x := by
    -- Differentiate the scalar cubic, then package it into the first basis direction.
    simpa [e0, ContinuousLinearMap.smulRight_apply, nsmul_eq_mul, smul_smul, mul_assoc,
      mul_left_comm, mul_comm] using
      (((hcoord0.pow 3).const_mul (32 : ℝ)).smul_const e0)
  have hterm0 :
      HasFDerivAt
        (fun y : Point ↦ (32 * y 0 ^ (3 : ℕ)) • e0)
        (((96 * x 0 ^ (2 : ℕ)) •
            ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0) : Point →L[ℝ] ℝ)).smulRight
          e0)
        x := by
    refine hscalar0.congr_fderiv ?_
    -- Convert the scalar derivative to the projected-coordinate normal form.
    ext v
    simp [e0, toDual_single_eq_smul_proj, ContinuousLinearMap.smulRight_apply]
    ring_nf
  have hscalar1 :
      HasFDerivAt
        (fun y : Point ↦ (-4 * y 1 ^ (3 : ℕ)) • e1)
        (((-((3 * (4 * x 1 ^ (2 : ℕ))) •
            InnerProductSpace.toDual ℝ Point (EuclideanSpace.single 1 (1 : ℝ)))).smulRight
          e1))
        x := by
    -- Differentiate the scalar cubic, then package it into the second basis direction.
    simpa [e1, ContinuousLinearMap.smulRight_apply, nsmul_eq_mul, smul_smul, mul_assoc,
      mul_left_comm, mul_comm] using
      (((hcoord1.pow 3).const_mul (-4 : ℝ)).smul_const e1)
  have hterm1 :
      HasFDerivAt
        (fun y : Point ↦ (-4 * y 1 ^ (3 : ℕ)) • e1)
        (((-12 * x 1 ^ (2 : ℕ)) •
            ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1) : Point →L[ℝ] ℝ)).smulRight
          e1)
        x := by
    refine hscalar1.congr_fderiv ?_
    -- Convert the scalar derivative to the projected-coordinate normal form.
    ext v
    simp [e1, toDual_single_eq_smul_proj, ContinuousLinearMap.smulRight_apply]
    ring_nf
  -- Reassemble the two coordinate contributions into the original Euclidean vector field.
  refine (hterm0.add hterm1).congr_of_eventuallyEq ?_
  filter_upwards with y
  ext i
  fin_cases i
  · simp [e0, e1]
  · simp [e0, e1]

/-- Helper for Chapter11 Exercise 11.4: along the normalized null-space direction, the Hessian
quadratic form simplifies to `48 x₀² - 6 x₁²`. -/
theorem chapter11Exercise114_projectedHessian_nullDirection_eq (x : Point) :
    hessianQuadraticAt chapter11Exercise113Objective x chapter11Exercise114NullDirection =
      48 * x 0 ^ (2 : ℕ) - 6 * x 1 ^ (2 : ℕ) := by
  -- Route correction: rewrite the gradient to the explicit cubic field first, then evaluate the
  -- resulting diagonal Hessian on the fixed null direction.
  have hgrad :
      gradient chapter11Exercise113Objective =
        fun y : Point ↦
          EuclideanSpace.single 0 (32 * y 0 ^ (3 : ℕ)) +
            EuclideanSpace.single 1 (-4 * y 1 ^ (3 : ℕ)) := by
    funext y
    exact chapter11Exercise114Objective_gradient_eq y
  rw [hessianQuadraticAt, hessianAt, hgrad]
  have hderiv := (chapter11Exercise114GradientField_hasFDerivAt x).fderiv
  rw [hderiv]
  -- Expand the diagonal linear map on the normalized null direction, then collapse the inner
  -- product to a scalar identity involving `(√2 / 2)^2 = 1/2`.
  have hsqrt : (Real.sqrt 2 : ℝ) ^ (2 : ℕ) = 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
  simp [ContinuousLinearMap.smulRight_apply, chapter11Exercise114NullDirection, PiLp.inner_apply,
    Fin.sum_univ_two]
  nlinarith

/-- Chapter11 Exercise 11.4 (1): at the point `(3, -2)ᵀ`, the projected gradient of the
reused constrained problem along the normalized null-space direction of `x 0 + x 1 = 1` is
`416 * √2`. -/
theorem chapter11Exercise114_projectedGradient_testPoint :
    projectedGradient114 chapter11Exercise114TestPoint chapter11Exercise114NullDirection =
      416 * Real.sqrt 2 := by
  -- The general projected-gradient formula reduces the test point to scalar arithmetic.
  rw [chapter11Exercise114_projectedGradient_nullDirection_eq]
  norm_num [chapter11Exercise114TestPoint]
  ring

/-- Chapter11 Exercise 11.4 (2): at the point `(3, -2)ᵀ`, the projected Hessian of the reused
constrained problem along the normalized null-space direction of `x 0 + x 1 = 1` is `408`. -/
theorem chapter11Exercise114_projectedHessian_testPoint :
    hessianQuadraticAt
        chapter11Exercise113Objective
        chapter11Exercise114TestPoint
        chapter11Exercise114NullDirection = 408 := by
  -- After the Hessian rewrite, the value at `(3, -2)` is immediate.
  rw [chapter11Exercise114_projectedHessian_nullDirection_eq]
  norm_num [chapter11Exercise114TestPoint]

/-- Chapter11 Exercise 11.4 (3): at the reused Exercise 11.3 solution
`chapter11Exercise113Solution = (-1, 2)ᵀ`, the projected gradient vanishes. -/
theorem chapter11Exercise114_projectedGradient_solution :
    projectedGradient114 chapter11Exercise113Solution chapter11Exercise114NullDirection = 0 :=
  by
  -- The explicit projected-gradient formula vanishes at the Exercise 11.3 optimizer.
  rw [chapter11Exercise114_projectedGradient_nullDirection_eq]
  norm_num [chapter11Exercise113Solution]

/-- Chapter11 Exercise 11.4 (4): at the reused Exercise 11.3 solution
`chapter11Exercise113Solution = (-1, 2)ᵀ`, the projected Hessian along the normalized
null-space direction of `x 0 + x 1 = 1` is `24`. -/
theorem chapter11Exercise114_projectedHessian_solution :
    hessianQuadraticAt
        chapter11Exercise113Objective
        chapter11Exercise113Solution
        chapter11Exercise114NullDirection = 24 := by
  -- The Hessian formula specializes to `24` at `(-1, 2)`.
  rw [chapter11Exercise114_projectedHessian_nullDirection_eq]
  norm_num [chapter11Exercise113Solution]

#print axioms chapter11Exercise114TestPoint
#print axioms chapter11Exercise114NullDirection
