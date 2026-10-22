/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Theorem_6_1_11

noncomputable section

open scoped Matrix.Norms.L2Operator

-- Domain sampling for this refine pass:
-- * `TrustRegionSubproblem` is the Chapter 6 owner of the quadratic trust-region model and its
--   Cauchy-point data.
-- * `TrustRegionSubproblem.gradientBoundaryStep`, `cauchyPointScale`, and `cauchyPoint` already
--   define the steepest-descent boundary step and trust-region Cauchy point for this exercise.
-- * `TrustRegionSubproblem.newtonStep`, `doubleDoglegGamma`,
--   `doubleDoglegIntermediateNewtonStep`, and `doubleDoglegPath` are the chapter owners of the
--   Newton step and dogleg/double-dogleg bridge data for the fixed quadratic model, with the
--   double-dogleg objects living in the positive-definite Hessian context of Chapter 6.
-- Source/core/bridge triage for this file:
-- * source-facing: the concrete exercise data and the first/second iterate formulas.
-- * core/canonical: `TrustRegionSubproblem` and its Chapter 6 dogleg/double-dogleg owners.
-- * bridge/view: the concrete `ℝ²` formulas for the exercise iterates and translated
--   point-equalities `x^(i + 1) = x^(i) + s`.
-- The first-iterate statements use those explicit coordinate bridges, while the second-iterate
-- statements refine to the updated stage-one `TrustRegionSubproblem` and its owner-level
-- `newtonStep`/`feasibleSet` API.

local notation "Point" => EuclideanSpace ℝ (Fin 2)
local notation "Matrix2" => Matrix (Fin 2) (Fin 2) ℝ

/-- The coordinate point `(a, b)ᵀ` in `EuclideanSpace ℝ (Fin 2)`. -/
def chapter06Exercise62Point (a b : ℝ) : Point :=
  WithLp.toLp 2 ![a, b]

/-- The quadratic objective `f(x) = (1 / 2) * x 0 ^ 2 + x 1 ^ 2` from the exercise. -/
def chapter06Exercise62Objective (x : Point) : ℝ :=
  ((1 : ℝ) / 2) * x 0 ^ (2 : ℕ) + x 1 ^ (2 : ℕ)

/-- The origin `(0, 0)ᵀ` in `ℝ²`. -/
def chapter06Exercise62Origin : Point :=
  chapter06Exercise62Point 0 0

/-- The gradient `∇f(x) = (x 0, 2 * x 1)ᵀ` of the exercise objective. -/
def chapter06Exercise62Gradient (x : Point) : Point :=
  chapter06Exercise62Point (x 0) ((2 : ℝ) * x 1)

/-- The starting point `x^(0) = (1, 1)ᵀ` from the exercise. -/
def chapter06Exercise62StartPoint : Point :=
  chapter06Exercise62Point 1 1

/-- The Hessian approximation `diag(1, 2)` of the exercise quadratic model. -/
def chapter06Exercise62HessianApprox : Matrix2 :=
  Matrix.diagonal ![(1 : ℝ), 2]

/-- The exercise Hessian approximation is symmetric. -/
theorem chapter06Exercise62HessianApprox_symm :
    chapter06Exercise62HessianApprox.IsSymm := by
  simp [chapter06Exercise62HessianApprox]

/-- The exercise Hessian approximation is positive definite. -/
theorem chapter06Exercise62HessianApprox_posDef :
    chapter06Exercise62HessianApprox.PosDef := by
  simp [chapter06Exercise62HessianApprox]

private def chapter06Exercise62SubproblemAt
    (x : Point) (Δ : ℝ) (hΔ : 0 < Δ) : TrustRegionSubproblem 2 where
  fAtCenter := chapter06Exercise62Objective x
  gradient := chapter06Exercise62Gradient x
  hessianApprox := chapter06Exercise62HessianApprox
  hessianApprox_symm := chapter06Exercise62HessianApprox_symm
  radius := Δ
  radius_pos := hΔ

/-- The first iterate for both dogleg and double-dogleg when `Δ₀ = 1`. -/
def chapter06Exercise62X1DeltaOnePoint : Point :=
  chapter06Exercise62Point (1 - 1 / Real.sqrt 5) (1 - 2 / Real.sqrt 5)

/-- The first dogleg iterate when `Δ₀ = 5 / 4`. -/
def chapter06Exercise62DoglegX1DeltaFiveQuartersPoint : Point :=
  chapter06Exercise62Point ((7 : ℝ) / 17) (-(7 : ℝ) / 68)

/-- The first double-dogleg iterate when `Δ₀ = 5 / 4`. -/
def chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint : Point :=
  chapter06Exercise62Point
    ((4 : ℝ) / 9 - Real.sqrt 5 / 18)
    (-(1 : ℝ) / 9 + Real.sqrt 5 / 36)

/-- The exercise trust-region subproblem with initial radius `Δ₀ = 1`. -/
def chapter06Exercise62SubproblemDeltaOne : TrustRegionSubproblem 2 :=
  chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint 1 (by norm_num)

/-- The exercise trust-region subproblem with initial radius `Δ₀ = 5 / 4`. -/
def chapter06Exercise62SubproblemDeltaFiveQuarters : TrustRegionSubproblem 2 :=
  chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4) (by norm_num)

/-- The exercise subproblem with `Δ₀ = 1` has a positive-definite Hessian approximation. -/
theorem chapter06Exercise62SubproblemDeltaOne_hessianApprox_posDef :
    chapter06Exercise62SubproblemDeltaOne.hessianApprox.PosDef := by
  simpa [chapter06Exercise62SubproblemDeltaOne, chapter06Exercise62SubproblemAt] using
    chapter06Exercise62HessianApprox_posDef

/-- The exercise subproblem with `Δ₀ = 5 / 4` has a positive-definite Hessian approximation. -/
theorem chapter06Exercise62SubproblemDeltaFiveQuarters_hessianApprox_posDef :
    chapter06Exercise62SubproblemDeltaFiveQuarters.hessianApprox.PosDef := by
  simpa [chapter06Exercise62SubproblemDeltaFiveQuarters, chapter06Exercise62SubproblemAt] using
    chapter06Exercise62HessianApprox_posDef

/-- The updated trust-region subproblem centered at the first double-dogleg iterate for
`Δ₀ = 1`. -/
def chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaOne : TrustRegionSubproblem 2 :=
  chapter06Exercise62SubproblemAt chapter06Exercise62X1DeltaOnePoint 1 (by norm_num)

/-- The updated trust-region subproblem centered at the first double-dogleg iterate for
`Δ₀ = 5 / 4`. -/
def chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaFiveQuarters :
    TrustRegionSubproblem 2 :=
  chapter06Exercise62SubproblemAt
    chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint
    ((5 : ℝ) / 4)
    (by norm_num)

/-- The updated stage-one subproblem for `Δ₀ = 1` has a positive-definite Hessian
approximation. -/
theorem chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaOne_hessianApprox_posDef :
    chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaOne.hessianApprox.PosDef := by
  simpa [chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaOne, chapter06Exercise62SubproblemAt]
    using chapter06Exercise62HessianApprox_posDef

/-- The updated stage-one subproblem for `Δ₀ = 5 / 4` has a positive-definite Hessian
approximation. -/
theorem chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaFiveQuarters_hessianApprox_posDef :
    chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaFiveQuarters.hessianApprox.PosDef := by
  simpa
      [chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaFiveQuarters,
        chapter06Exercise62SubproblemAt]
    using chapter06Exercise62HessianApprox_posDef

/-- Helper for Chapter06 Exercise 6.2: `√5` satisfies the defining square identity. -/
theorem chapter06Exercise62_sqrtFive_sq : Real.sqrt 5 ^ (2 : ℕ) = 5 := by
  -- This records the only irrational arithmetic identity used in the concrete norm checks.
  simpa [pow_two] using Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)

/-- Helper for Chapter06 Exercise 6.2: the Euclidean norm square of `(a, b)ᵀ` is `a^2 + b^2`. -/
theorem chapter06Exercise62Point_norm_sq (a b : ℝ) :
    ‖chapter06Exercise62Point a b‖ ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
  -- Convert the norm square to the coordinate dot product once.
  simpa [chapter06Exercise62Point, dotProduct, pow_two] using
    (EuclideanSpace.real_norm_sq_eq (chapter06Exercise62Point a b))

/-- Helper for Chapter06 Exercise 6.2: the starting gradient `(1, 2)ᵀ` has norm `√5`. -/
theorem chapter06Exercise62StartGradient_norm :
    ‖chapter06Exercise62Gradient chapter06Exercise62StartPoint‖ = Real.sqrt 5 := by
  have hsq :
      ‖chapter06Exercise62Gradient chapter06Exercise62StartPoint‖ ^ (2 : ℕ) = 5 := by
    have hsq' := chapter06Exercise62Point_norm_sq 1 2
    norm_num at hsq'
    simpa [chapter06Exercise62Gradient, chapter06Exercise62StartPoint, chapter06Exercise62Point] using
      hsq'
  have hnonneg : 0 ≤ ‖chapter06Exercise62Gradient chapter06Exercise62StartPoint‖ := norm_nonneg _
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  -- The norm is the nonnegative square root of `5`.
  nlinarith [hsq, chapter06Exercise62_sqrtFive_sq]

/-- Helper for Chapter06 Exercise 6.2: the initial curvature term `gᵀBg` is `9`. -/
theorem chapter06Exercise62SubproblemAtStart_gradientCurvature_eq
    (Δ : ℝ) (hΔ : 0 < Δ) :
    (chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint Δ hΔ).gradientCurvature = 9 := by
  -- The starting gradient is `(1, 2)ᵀ` and the Hessian is `diag(1, 2)`.
  norm_num [TrustRegionSubproblem.gradientCurvature, chapter06Exercise62SubproblemAt,
    Matrix.mulVec, dotProduct,
    dotProduct,
    chapter06Exercise62StartPoint, chapter06Exercise62Gradient, chapter06Exercise62Point,
    chapter06Exercise62HessianApprox]

/-- Helper for Chapter06 Exercise 6.2: the inverse Hessian `diag(1, 1 / 2)` sends the exercise
gradient `(x₁, 2 x₂)ᵀ` back to the center coordinates `(x₁, x₂)ᵀ`. -/
theorem chapter06Exercise62HessianInv_mulVec_gradient (x : Point) :
    (chapter06Exercise62HessianApprox⁻¹).mulVec (chapter06Exercise62Gradient x).ofLp = x.ofLp :=
  by
  -- Route correction: use the inverse-matrix identity on the concrete Hessian instead of
  -- normalizing `Ring.inverse ![1, 2]` coordinatewise.
  have hmul :
      chapter06Exercise62HessianApprox.mulVec x.ofLp = (chapter06Exercise62Gradient x).ofLp := by
    -- The diagonal Hessian acts coordinatewise as `(x₁, x₂) ↦ (x₁, 2 x₂)`.
    ext i <;> fin_cases i <;>
      simp [chapter06Exercise62HessianApprox, chapter06Exercise62Gradient,
        chapter06Exercise62Point, Matrix.mulVec]
  letI := chapter06Exercise62HessianApprox_posDef.isUnit.invertible
  -- Apply `B⁻¹` to the already-normalized identity `B x = ∇f(x)`.
  calc
    (chapter06Exercise62HessianApprox⁻¹).mulVec (chapter06Exercise62Gradient x).ofLp
        = (chapter06Exercise62HessianApprox⁻¹).mulVec
            (chapter06Exercise62HessianApprox.mulVec x.ofLp) := by
            rw [← hmul]
    _ = ((chapter06Exercise62HessianApprox⁻¹) * chapter06Exercise62HessianApprox).mulVec x.ofLp :=
          by
            exact Matrix.mulVec_mulVec x.ofLp
              (chapter06Exercise62HessianApprox⁻¹) chapter06Exercise62HessianApprox
    _ = x.ofLp := by
          simp

/-- Helper for Chapter06 Exercise 6.2: every concrete subproblem in this exercise keeps the
fixed positive-definite Hessian `diag(1, 2)`. -/
theorem chapter06Exercise62SubproblemAt_hessianApprox_posDef
    (x : Point) (Δ : ℝ) (hΔ : 0 < Δ) :
    (chapter06Exercise62SubproblemAt x Δ hΔ).hessianApprox.PosDef := by
  -- The subproblem stores the exercise Hessian verbatim, so positivity is unchanged.
  simpa [chapter06Exercise62SubproblemAt] using chapter06Exercise62HessianApprox_posDef

/-- Helper for Chapter06 Exercise 6.2: the literal Cauchy-scale minimum for `Δ₀ = 1` truncates
at the trust-region boundary. -/
theorem chapter06Exercise62DeltaOneRatioMin_eq_one :
    min (((5 : ℝ) * Real.sqrt 5) / 9) 1 = 1 := by
  -- The ratio `5 * √5 / 9` is at least `1`, so the Cauchy scale saturates at the boundary.
  apply min_eq_right
  nlinarith [chapter06Exercise62_sqrtFive_sq, Real.sqrt_nonneg 5]

/-- Helper for Chapter06 Exercise 6.2: for `Δ₀ = 1`, the Cauchy scale is `1` and the boundary
steepest-descent step is `(-1 / √5, -2 / √5)ᵀ`. -/
theorem chapter06Exercise62SubproblemDeltaOne_firstStepData :
    let P := chapter06Exercise62SubproblemDeltaOne
    P.cauchyPointScale = 1 ∧
      P.gradientBoundaryStep =
        chapter06Exercise62Point (-(1 : ℝ) / Real.sqrt 5) (-(2 : ℝ) / Real.sqrt 5) :=
  by
  dsimp [chapter06Exercise62SubproblemDeltaOne]
  have hgrad_norm :
      ‖(chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint 1 (by norm_num)).gradient‖ =
        Real.sqrt 5 := by
    -- The initial gradient is the same `(1, 2)ᵀ` vector as in the other radius case.
    simpa [chapter06Exercise62SubproblemAt] using chapter06Exercise62StartGradient_norm
  have hcurv_eq :
      (chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint 1
        (by norm_num)).gradientCurvature = 9 :=
    chapter06Exercise62SubproblemAtStart_gradientCurvature_eq 1 (by norm_num)
  have hscale :
      (chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint 1
        (by norm_num)).cauchyPointScale = 1 := by
    have hcurv :
        0 <
          (chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint 1
            (by norm_num)).gradientCurvature := by
      rw [hcurv_eq]
      norm_num
    have hgrad_cube :
        ‖(chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint 1
            (by norm_num)).gradient‖ ^ (3 : ℕ) =
          (5 : ℝ) * Real.sqrt 5 := by
      rw [hgrad_norm]
      calc
        Real.sqrt 5 ^ (3 : ℕ) = Real.sqrt 5 * (Real.sqrt 5 ^ (2 : ℕ)) := by ring
        _ = (5 : ℝ) * Real.sqrt 5 := by
              rw [chapter06Exercise62_sqrtFive_sq]
              ring
    have hratio_eq :
        ‖(chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint 1
              (by norm_num)).gradient‖ ^ (3 : ℕ) /
            ((chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint 1
                (by norm_num)).radius *
              (chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint 1
                (by norm_num)).gradientCurvature) =
          (5 : ℝ) * Real.sqrt 5 / 9 := by
      rw [hgrad_cube, hcurv_eq]
      norm_num [chapter06Exercise62SubproblemAt]
    -- Route correction: isolate the exact minimum value before simplifying the boundary step.
    rw [TrustRegionSubproblem.cauchyPointScale_eq_min_of_pos_curvature _ hcurv, hratio_eq,
      chapter06Exercise62DeltaOneRatioMin_eq_one]
  constructor
  · exact hscale
  · have hgrad :
        (chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint 1
          (by norm_num)).gradient ≠ 0 := by
        intro hzero
        have hzero0 := congrArg (fun y : Point ↦ y 0) hzero
        norm_num [chapter06Exercise62SubproblemAt, chapter06Exercise62StartPoint,
          chapter06Exercise62Gradient, chapter06Exercise62Point] at hzero0
    have hnorm_vec : ‖(!₂[1, 2] : Point)‖ = Real.sqrt 5 := by
      -- The concrete gradient vector has the same norm as the starting gradient.
      simpa [chapter06Exercise62SubproblemAt, chapter06Exercise62StartPoint,
        chapter06Exercise62Gradient, chapter06Exercise62Point] using hgrad_norm
    -- Rewrite the owner-level gradient boundary step to the normalized negative gradient.
    rw [TrustRegionSubproblem.gradientBoundaryStep_eq_of_ne_zero _ hgrad]
    ext i <;> fin_cases i <;>
      simp [chapter06Exercise62SubproblemAt, chapter06Exercise62StartPoint,
        chapter06Exercise62Gradient, chapter06Exercise62Point]
      <;> rw [hnorm_vec]
      <;> field_simp [Real.sqrt_ne_zero'.2 (show (0 : ℝ) < 5 by norm_num)]
      <;> ring_nf

/-- Helper for Chapter06 Exercise 6.2: for `Δ₀ = 5 / 4`, the Cauchy scale is
`4 * √5 / 9` and the Cauchy point is `(-5 / 9, -10 / 9)ᵀ`. -/
theorem chapter06Exercise62SubproblemDeltaFiveQuarters_cauchyData :
    let P := chapter06Exercise62SubproblemDeltaFiveQuarters
    P.cauchyPointScale = (4 : ℝ) * Real.sqrt 5 / 9 ∧
      P.cauchyPoint = chapter06Exercise62Point (-(5 : ℝ) / 9) (-(10 : ℝ) / 9) := by
  dsimp [chapter06Exercise62SubproblemDeltaFiveQuarters]
  have hgrad_norm :
      ‖(chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
          (by norm_num)).gradient‖ = Real.sqrt 5 := by
    simpa [chapter06Exercise62SubproblemAt] using chapter06Exercise62StartGradient_norm
  have hcurv_eq :
      (chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
        (by norm_num)).gradientCurvature = 9 :=
    chapter06Exercise62SubproblemAtStart_gradientCurvature_eq ((5 : ℝ) / 4) (by norm_num)
  have hscale :
      (chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
        (by norm_num)).cauchyPointScale = (4 : ℝ) * Real.sqrt 5 / 9 := by
    have hcurv :
        0 <
          (chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
            (by norm_num)).gradientCurvature := by
      rw [hcurv_eq]
      norm_num
    have hgrad_cube :
        ‖(chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
            (by norm_num)).gradient‖ ^ (3 : ℕ) =
          (5 : ℝ) * Real.sqrt 5 := by
      rw [hgrad_norm]
      calc
        Real.sqrt 5 ^ (3 : ℕ) = Real.sqrt 5 * (Real.sqrt 5 ^ (2 : ℕ)) := by ring
        _ = (5 : ℝ) * Real.sqrt 5 := by rw [chapter06Exercise62_sqrtFive_sq]; ring
    have hratio_le_one : (4 : ℝ) * Real.sqrt 5 / 9 ≤ 1 := by
      nlinarith [chapter06Exercise62_sqrtFive_sq]
    have hmin : min ((4 : ℝ) * Real.sqrt 5 / 9) 1 = (4 : ℝ) * Real.sqrt 5 / 9 :=
      min_eq_left hratio_le_one
    have hratio_eq :
        ‖(chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
              (by norm_num)).gradient‖ ^ (3 : ℕ) /
            ((chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
                (by norm_num)).radius *
              (chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
                (by norm_num)).gradientCurvature) =
          (4 : ℝ) * Real.sqrt 5 / 9 := by
      rw [hgrad_cube, hcurv_eq]
      norm_num [chapter06Exercise62SubproblemAt]
      field_simp
      ring
    rw [TrustRegionSubproblem.cauchyPointScale_eq_min_of_pos_curvature _ hcurv, hratio_eq, hmin]
  constructor
  · exact hscale
  · -- Expand the canonical Cauchy-point formula after fixing the concrete scale.
    have hgrad :
        (chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
          (by norm_num)).gradient ≠ 0 := by
      intro hzero
      have hzero0 := congrArg (fun y : Point ↦ y 0) hzero
      norm_num [chapter06Exercise62SubproblemAt, chapter06Exercise62StartPoint,
        chapter06Exercise62Gradient, chapter06Exercise62Point] at hzero0
    have hnorm_vec : ‖(!₂[1, 2] : Point)‖ = Real.sqrt 5 := by
      have hsq : ‖(!₂[1, 2] : Point)‖ ^ (2 : ℕ) = 5 := by
        have hsq' := chapter06Exercise62Point_norm_sq 1 2
        norm_num at hsq'
        simpa [chapter06Exercise62Point] using hsq'
      have hnonneg : 0 ≤ ‖(!₂[1, 2] : Point)‖ := norm_nonneg _
      have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
      have hle : ‖(!₂[1, 2] : Point)‖ ≤ Real.sqrt 5 := by
        nlinarith [hsq, chapter06Exercise62_sqrtFive_sq]
      have hge : Real.sqrt 5 ≤ ‖(!₂[1, 2] : Point)‖ := by
        nlinarith [hsq, chapter06Exercise62_sqrtFive_sq]
      exact le_antisymm hle hge
    rw [TrustRegionSubproblem.cauchyPoint_eq_of_ne_zero _ hgrad]
    rw [hscale]
    ext i <;> fin_cases i <;>
      simp [chapter06Exercise62SubproblemAt, chapter06Exercise62StartPoint,
        chapter06Exercise62Gradient, chapter06Exercise62Point, chapter06Exercise62HessianApprox]
      <;> rw [hnorm_vec]
      <;> field_simp [Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 5)]
      <;> ring_nf

/-- Helper for Chapter06 Exercise 6.2: the Newton step of the concrete quadratic subproblem at
center `x` is exactly `-x`. -/
theorem chapter06Exercise62SubproblemAt_newtonStep_eq_negCenter
    (x : Point) (Δ : ℝ) (hΔ : 0 < Δ) :
    let P := chapter06Exercise62SubproblemAt x Δ hΔ
    P.newtonStep (chapter06Exercise62SubproblemAt_hessianApprox_posDef x Δ hΔ).isUnit = -x := by
  dsimp
  -- Rewrite the owner-level Newton step to the inverse-Hessian action in coordinates.
  have hstep :
      ((chapter06Exercise62SubproblemAt x Δ hΔ).newtonStep
          (chapter06Exercise62SubproblemAt_hessianApprox_posDef x Δ hΔ).isUnit).ofLp =
        -((chapter06Exercise62HessianApprox⁻¹).mulVec (chapter06Exercise62Gradient x).ofLp) := by
    simpa [chapter06Exercise62SubproblemAt] using
      (chapter06Exercise62SubproblemAt x Δ hΔ).ofLp_newtonStep_eq_neg_mulVec_inv
        (chapter06Exercise62SubproblemAt_hessianApprox_posDef x Δ hΔ).isUnit
  ext i <;> fin_cases i
  · -- The first coordinate inverts the `1` entry of `diag(1, 2)` and becomes `-x 0`.
    have h0 := congrFun hstep 0
    simpa [chapter06Exercise62HessianInv_mulVec_gradient] using h0
  · -- The second coordinate inverts the `2` entry of `diag(1, 2)` and becomes `-x 1`.
    have h1 := congrFun hstep 1
    simpa [chapter06Exercise62HessianInv_mulVec_gradient] using h1

/-- Helper for Chapter06 Exercise 6.2: for `Δ₀ = 5 / 4`, the canonical double-dogleg ratio is
`25 / 27`. -/
theorem chapter06Exercise62SubproblemDeltaFiveQuarters_doubleDoglegGamma_eq :
    let P := chapter06Exercise62SubproblemDeltaFiveQuarters
    P.doubleDoglegGamma (chapter06Exercise62SubproblemDeltaFiveQuarters_hessianApprox_posDef.isUnit)
      = (25 : ℝ) / 27 := by
  dsimp [chapter06Exercise62SubproblemDeltaFiveQuarters]
  have hgrad_norm :
      ‖(chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
          (by norm_num)).gradient‖ = Real.sqrt 5 := by
    -- The concrete gradient stays `(1, 2)ᵀ`, so the norm data is unchanged.
    simpa [chapter06Exercise62SubproblemAt] using chapter06Exercise62StartGradient_norm
  have hnorm_four :
      ‖(chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
          (by norm_num)).gradient‖ ^ (4 : ℕ) = 25 := by
    rw [hgrad_norm]
    calc
      Real.sqrt 5 ^ (4 : ℕ) = (Real.sqrt 5 ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = 25 := by
            rw [chapter06Exercise62_sqrtFive_sq]
            norm_num
  have hcurv_eq :
      (chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
        (by norm_num)).gradientCurvature = 9 :=
    chapter06Exercise62SubproblemAtStart_gradientCurvature_eq ((5 : ℝ) / 4) (by norm_num)
  have hnewton_eq :
      (chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
          (by norm_num)).newtonStep
          (chapter06Exercise62SubproblemAt_hessianApprox_posDef
            chapter06Exercise62StartPoint ((5 : ℝ) / 4) (by norm_num)).isUnit =
        -chapter06Exercise62StartPoint := by
    -- The Newton step is the negative center for every concrete subproblem in this file.
    simpa using
      chapter06Exercise62SubproblemAt_newtonStep_eq_negCenter
        chapter06Exercise62StartPoint ((5 : ℝ) / 4) (by norm_num)
  have hnewton_dot :
      -dotProduct
          (chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
            (by norm_num)).gradient
          ((chapter06Exercise62SubproblemAt chapter06Exercise62StartPoint ((5 : ℝ) / 4)
            (by norm_num)).newtonStep
            (chapter06Exercise62SubproblemAt_hessianApprox_posDef
              chapter06Exercise62StartPoint ((5 : ℝ) / 4) (by norm_num)).isUnit) =
        3 := by
    -- The denominator factor `-gᵀ sᴺ` reduces to `3` for `g = (1, 2)` and `sᴺ = (-1, -1)`.
    rw [hnewton_eq]
    norm_num [chapter06Exercise62SubproblemAt, chapter06Exercise62StartPoint,
      chapter06Exercise62Gradient, chapter06Exercise62Point, dotProduct, Fin.sum_univ_two]
  -- Evaluate the Chapter 6 gamma formula on the explicit quadratic data.
  rw [TrustRegionSubproblem.doubleDoglegGamma, hnorm_four, hcurv_eq, hnewton_dot]
  norm_num

/-- Helper for Chapter06 Exercise 6.2: if `‖x‖ ≤ Δ`, then the Newton step `-x` is feasible for
the concrete subproblem centered at `x`. -/
theorem chapter06Exercise62NegCenter_mem_feasibleSet_of_norm_le
    (x : Point) (Δ : ℝ) (hΔ : 0 < Δ) (hx : ‖x‖ ≤ Δ) :
    let P := chapter06Exercise62SubproblemAt x Δ hΔ
    (-x) ∈ P.feasibleSet := by
  dsimp
  -- Feasibility is exactly the trust-region norm bound, and `‖-x‖ = ‖x‖`.
  rw [TrustRegionSubproblem.mem_feasibleSet_iff]
  simpa [chapter06Exercise62SubproblemAt] using hx

/-- The dogleg first iterate for Chapter06 Exercise 6.2: for the quadratic objective
`f(x) = (1 / 2) * x 0 ^ 2 + x 1 ^ 2`, starting point `(1, 1)ᵀ`, and initial trust-region radius
`Δ₀ = 1`, the dogleg method gives the first iterate
`x^(1) = (1 - 1 / √5, 1 - 2 / √5)ᵀ`. -/
theorem chapter06Exercise62DoglegX1DeltaOne :
    let P := chapter06Exercise62SubproblemDeltaOne
    P.cauchyPointScale = 1 ∧
      chapter06Exercise62X1DeltaOnePoint = chapter06Exercise62StartPoint + P.gradientBoundaryStep :=
  by
  dsimp
  rcases chapter06Exercise62SubproblemDeltaOne_firstStepData with ⟨hscale, hstep⟩
  constructor
  · exact hscale
  · -- Translate the explicit boundary step back to the iterate formula from the exercise.
    rw [hstep]
    ext i <;> fin_cases i <;>
      simp [chapter06Exercise62X1DeltaOnePoint, chapter06Exercise62StartPoint,
        chapter06Exercise62Point]
      <;> ring_nf

/-- The dogleg first iterate for Chapter06 Exercise 6.2 with `Δ₀ = 5 / 4`: for the quadratic
objective
`f(x) = (1 / 2) * x 0 ^ 2 + x 1 ^ 2`, starting point `(1, 1)ᵀ`, and initial trust-region radius
`Δ₀ = 5 / 4`, the dogleg method gives the first iterate
`x^(1) = (7 / 17, -7 / 68)ᵀ`. -/
theorem chapter06Exercise62DoglegX1DeltaFiveQuarters :
    let P := chapter06Exercise62SubproblemDeltaFiveQuarters
    P.cauchyPointScale < 1 ∧
      ∃ θ ∈ Set.Icc (0 : ℝ) 1,
        chapter06Exercise62DoglegX1DeltaFiveQuartersPoint =
          chapter06Exercise62StartPoint +
            P.doglegPath
              (chapter06Exercise62SubproblemDeltaFiveQuarters_hessianApprox_posDef.isUnit)
              (1 + θ) ∧
          dist chapter06Exercise62StartPoint
            chapter06Exercise62DoglegX1DeltaFiveQuartersPoint = P.radius := by
  dsimp
  rcases chapter06Exercise62SubproblemDeltaFiveQuarters_cauchyData with ⟨hscale, hcauchy⟩
  have hscale_lt : (4 : ℝ) * Real.sqrt 5 / 9 < 1 := by
    -- The Cauchy point is strictly inside the radius-`5/4` trust region.
    nlinarith [chapter06Exercise62_sqrtFive_sq, Real.sqrt_nonneg 5]
  constructor
  · rw [hscale]
    exact hscale_lt
  · refine ⟨(5 : ℝ) / 68, ?_, ?_, ?_⟩
    · constructor <;> norm_num
    · -- Move to the second dogleg branch and evaluate the affine interpolation in coordinates.
      have hnewton_eq :
          chapter06Exercise62SubproblemDeltaFiveQuarters.newtonStep
              (chapter06Exercise62SubproblemDeltaFiveQuarters_hessianApprox_posDef.isUnit) =
            -chapter06Exercise62StartPoint := by
        simpa [chapter06Exercise62SubproblemDeltaFiveQuarters] using
          chapter06Exercise62SubproblemAt_newtonStep_eq_negCenter
            chapter06Exercise62StartPoint ((5 : ℝ) / 4) (by norm_num)
      rw [TrustRegionSubproblem.doglegPath_eq_cauchyPoint_add_smul_of_one_lt _ _ _
        (by norm_num)]
      rw [hcauchy, hnewton_eq]
      ext i <;> fin_cases i <;>
        simp [chapter06Exercise62DoglegX1DeltaFiveQuartersPoint, chapter06Exercise62StartPoint,
          chapter06Exercise62Point]
        <;> ring_nf
    · -- The explicit iterate lies on the trust-region boundary because its displacement norm is
      -- exactly `5 / 4`.
      rw [dist_eq_norm]
      have hsq :
          ‖chapter06Exercise62StartPoint - chapter06Exercise62DoglegX1DeltaFiveQuartersPoint‖ ^
              (2 : ℕ) =
            ((5 : ℝ) / 4) ^ (2 : ℕ) := by
        rw [show
            chapter06Exercise62StartPoint - chapter06Exercise62DoglegX1DeltaFiveQuartersPoint =
              chapter06Exercise62Point ((10 : ℝ) / 17) ((75 : ℝ) / 68) by
              ext i <;> fin_cases i <;>
                simp [chapter06Exercise62StartPoint,
                  chapter06Exercise62DoglegX1DeltaFiveQuartersPoint, chapter06Exercise62Point]
                <;> ring]
        rw [chapter06Exercise62Point_norm_sq]
        norm_num
      have hnonneg :
          0 ≤ ‖chapter06Exercise62StartPoint - chapter06Exercise62DoglegX1DeltaFiveQuartersPoint‖ :=
        norm_nonneg _
      have hdist :
          ‖chapter06Exercise62StartPoint - chapter06Exercise62DoglegX1DeltaFiveQuartersPoint‖ =
            (5 : ℝ) / 4 := by
        nlinarith
      simpa [chapter06Exercise62SubproblemDeltaFiveQuarters, chapter06Exercise62SubproblemAt]
        using hdist

/-- For `Δ₀ = 1`, the exercise's double-dogleg method gives the first iterate
`x^(1) = (1 - 1 / √5, 1 - 2 / √5)ᵀ`. -/
theorem chapter06Exercise62DoubleDoglegX1DeltaOne :
    let P := chapter06Exercise62SubproblemDeltaOne
    P.cauchyPointScale = 1 ∧
      chapter06Exercise62X1DeltaOnePoint = chapter06Exercise62StartPoint + P.gradientBoundaryStep :=
  by
  -- For `Δ₀ = 1`, the dogleg and double-dogleg first-iterate statements coincide verbatim.
  exact chapter06Exercise62DoglegX1DeltaOne

/-- For `Δ₀ = 5 / 4`, the exercise's double-dogleg method gives the first iterate
`x^(1) = (4 / 9 - √5 / 18, -1 / 9 + √5 / 36)ᵀ`. -/
theorem chapter06Exercise62DoubleDoglegX1DeltaFiveQuarters :
    let P := chapter06Exercise62SubproblemDeltaFiveQuarters
    P.cauchyPointScale < 1 ∧
      ∃ θ ∈ Set.Icc (0 : ℝ) 1,
        chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint =
          chapter06Exercise62StartPoint +
            P.doubleDoglegPath
              (chapter06Exercise62SubproblemDeltaFiveQuarters_hessianApprox_posDef.isUnit)
              (P.doubleDoglegGamma
              (chapter06Exercise62SubproblemDeltaFiveQuarters_hessianApprox_posDef.isUnit))
              (1 + θ) ∧
          dist chapter06Exercise62StartPoint
            chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint = P.radius := by
  dsimp
  rcases chapter06Exercise62SubproblemDeltaFiveQuarters_cauchyData with ⟨hscale, hcauchy⟩
  have hscale_lt : (4 : ℝ) * Real.sqrt 5 / 9 < 1 := by
    -- The same strict inequality places the iterate on the second double-dogleg leg.
    nlinarith [chapter06Exercise62_sqrtFive_sq, Real.sqrt_nonneg 5]
  constructor
  · rw [hscale]
    exact hscale_lt
  · let θ : ℝ := (3 : ℝ) * Real.sqrt 5 / 20
    have hθ_nonneg : 0 ≤ θ := by
      -- The witness is a positive multiple of `√5`.
      dsimp [θ]
      positivity
    have hθ_pos : 0 < θ := by
      -- This keeps the point strictly on the second path segment.
      dsimp [θ]
      positivity
    have hθ_le_one : θ ≤ 1 := by
      -- Squaring shows `3 * √5 / 20 ≤ 1`.
      dsimp [θ]
      nlinarith [chapter06Exercise62_sqrtFive_sq, Real.sqrt_nonneg 5]
    refine ⟨θ, ⟨hθ_nonneg, hθ_le_one⟩, ?_, ?_⟩
    · -- Route correction: rewrite the owner path at the solved gamma value before doing the
      -- coordinate algebra.
      have hnewton_eq :
          chapter06Exercise62SubproblemDeltaFiveQuarters.newtonStep
              (chapter06Exercise62SubproblemDeltaFiveQuarters_hessianApprox_posDef.isUnit) =
            -chapter06Exercise62StartPoint := by
        simpa [chapter06Exercise62SubproblemDeltaFiveQuarters] using
          chapter06Exercise62SubproblemAt_newtonStep_eq_negCenter
            chapter06Exercise62StartPoint ((5 : ℝ) / 4) (by norm_num)
      rw [chapter06Exercise62SubproblemDeltaFiveQuarters_doubleDoglegGamma_eq]
      rw [TrustRegionSubproblem.doubleDoglegPath_eq_cauchyPoint_add_smul_of_one_lt_of_le_two
        _ _ _ _ (by linarith [hθ_pos]) (by linarith [hθ_le_one])]
      rw [hcauchy, TrustRegionSubproblem.doubleDoglegIntermediateNewtonStep, hnewton_eq]
      ext i <;> fin_cases i <;>
        simp [chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint,
          chapter06Exercise62StartPoint, chapter06Exercise62Point, θ]
        <;> field_simp [Real.sqrt_ne_zero'.2 (show (0 : ℝ) < 5 by norm_num)]
        <;> ring_nf
    · -- The explicit iterate again lies on the trust-region boundary.
      rw [dist_eq_norm]
      have hsq :
          ‖chapter06Exercise62StartPoint -
              chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint‖ ^ (2 : ℕ) =
            ((5 : ℝ) / 4) ^ (2 : ℕ) := by
        rw [show
            chapter06Exercise62StartPoint -
                chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint =
              chapter06Exercise62Point
                ((5 : ℝ) / 9 + Real.sqrt 5 / 18)
                ((10 : ℝ) / 9 - Real.sqrt 5 / 36) by
              ext i <;> fin_cases i <;>
                simp [chapter06Exercise62StartPoint,
                  chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint,
                  chapter06Exercise62Point]
                <;> ring]
        rw [chapter06Exercise62Point_norm_sq]
        nlinarith [chapter06Exercise62_sqrtFive_sq]
      have hnonneg :
          0 ≤
            ‖chapter06Exercise62StartPoint -
                chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint‖ :=
        norm_nonneg _
      have hdist :
          ‖chapter06Exercise62StartPoint -
              chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint‖ =
            (5 : ℝ) / 4 := by
        nlinarith
      simpa [chapter06Exercise62SubproblemDeltaFiveQuarters, chapter06Exercise62SubproblemAt]
        using hdist

/-- The `Δ₀ = 1` second double-dogleg iterate for Chapter06 Exercise 6.2: for the quadratic
objective
`f(x) = (1 / 2) * x 0 ^ 2 + x 1 ^ 2`, starting point `(1, 1)ᵀ`, and initial trust-region radius
`Δ₀ = 1`, the updated stage-one subproblem at the first double-dogleg iterate
`x^(1) = (1 - 1 / √5, 1 - 2 / √5)ᵀ` has a feasible Newton step, and that Newton step sends
`x^(1)` to `x^(2) = (0, 0)ᵀ`. -/
theorem chapter06Exercise62DoubleDoglegX2DeltaOne :
    let P := chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaOne
    let hP := chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaOne_hessianApprox_posDef
    P.newtonStep (hP.isUnit) ∈ P.feasibleSet ∧
      chapter06Exercise62X1DeltaOnePoint +
          P.newtonStep (hP.isUnit) =
        chapter06Exercise62Origin := by
  dsimp
  have hstep :
      chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaOne.newtonStep
          (chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaOne_hessianApprox_posDef.isUnit) =
        -chapter06Exercise62X1DeltaOnePoint := by
    -- The stage-one Newton step is still `-center`.
    simpa [chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaOne] using
      chapter06Exercise62SubproblemAt_newtonStep_eq_negCenter
        chapter06Exercise62X1DeltaOnePoint 1 (by norm_num)
  have hcenter_le :
      ‖chapter06Exercise62X1DeltaOnePoint‖ ≤ 1 := by
    -- The first iterate for `Δ₀ = 1` lies inside the radius-`1` trust region.
    have hsq :
        ‖chapter06Exercise62X1DeltaOnePoint‖ ^ (2 : ℕ) =
          3 - 6 / Real.sqrt 5 := by
      rw [chapter06Exercise62X1DeltaOnePoint, chapter06Exercise62Point_norm_sq]
      field_simp [Real.sqrt_ne_zero'.2 (show (0 : ℝ) < 5 by norm_num)]
      nlinarith [chapter06Exercise62_sqrtFive_sq]
    have hnonneg : 0 ≤ ‖chapter06Exercise62X1DeltaOnePoint‖ := norm_nonneg _
    have hsq_le : ‖chapter06Exercise62X1DeltaOnePoint‖ ^ (2 : ℕ) ≤ 1 := by
      have haux : 3 - 6 / Real.sqrt 5 ≤ 1 := by
        have hsqrt_pos : 0 < Real.sqrt 5 := by
          positivity
        have hbound : 2 * Real.sqrt 5 ≤ 6 := by
          nlinarith [chapter06Exercise62_sqrtFive_sq, Real.sqrt_nonneg 5]
        have hbound' : 2 ≤ 6 / Real.sqrt 5 := by
          exact (le_div_iff₀ hsqrt_pos).2 (by simpa [mul_comm] using hbound)
        linarith
      rw [hsq]
      exact haux
    nlinarith
  constructor
  · rw [hstep]
    exact chapter06Exercise62NegCenter_mem_feasibleSet_of_norm_le
      chapter06Exercise62X1DeltaOnePoint 1 (by norm_num) hcenter_le
  · rw [hstep]
    -- Adding the Newton step `-x^(1)` cancels the stage-one center.
    ext i <;> fin_cases i <;>
      simp [chapter06Exercise62X1DeltaOnePoint, chapter06Exercise62Origin,
        chapter06Exercise62Point]
      <;> ring_nf

/-- Chapter06 Exercise 6.2: for the quadratic objective
`f(x) = (1 / 2) * x 0 ^ 2 + x 1 ^ 2`, starting point `(1, 1)ᵀ`, and initial trust-region radius
`Δ₀ = 5 / 4`, the updated stage-one subproblem at the first double-dogleg iterate
`x^(1) = (4 / 9 - √5 / 18, -1 / 9 + √5 / 36)ᵀ` has a feasible Newton step, and that Newton
step sends `x^(1)` to `x^(2) = (0, 0)ᵀ`. -/
theorem chapter06Exercise62DoubleDoglegX2DeltaFiveQuarters :
    let P := chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaFiveQuarters
    let hP :=
      chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaFiveQuarters_hessianApprox_posDef
    P.newtonStep (hP.isUnit) ∈ P.feasibleSet ∧
      chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint +
          P.newtonStep (hP.isUnit) =
        chapter06Exercise62Origin := by
  dsimp
  have hstep :
      chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaFiveQuarters.newtonStep
          (chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaFiveQuarters_hessianApprox_posDef.isUnit) =
        -chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint := by
    -- The same Newton-step formula applies after translating the subproblem center.
    simpa [chapter06Exercise62DoubleDoglegStageOneSubproblemDeltaFiveQuarters] using
      chapter06Exercise62SubproblemAt_newtonStep_eq_negCenter
        chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint ((5 : ℝ) / 4) (by norm_num)
  have hcenter_le :
      ‖chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint‖ ≤ (5 : ℝ) / 4 := by
    -- The explicit first double-dogleg iterate is well inside the radius-`5/4` trust region.
    have hsq :
        ‖chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint‖ ^ (2 : ℕ) =
          (11 : ℝ) / 48 - Real.sqrt 5 / 18 := by
      rw [chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint,
        chapter06Exercise62Point_norm_sq]
      field_simp [Real.sqrt_ne_zero'.2 (show (0 : ℝ) < 5 by norm_num)]
      nlinarith [chapter06Exercise62_sqrtFive_sq]
    have hnonneg : 0 ≤ ‖chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint‖ := norm_nonneg _
    have hsq_le :
        ‖chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint‖ ^ (2 : ℕ) ≤
          ((5 : ℝ) / 4) ^ (2 : ℕ) := by
      nlinarith [hsq, chapter06Exercise62_sqrtFive_sq, Real.sqrt_nonneg 5]
    nlinarith
  constructor
  · rw [hstep]
    exact chapter06Exercise62NegCenter_mem_feasibleSet_of_norm_le
      chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint ((5 : ℝ) / 4)
      (by norm_num) hcenter_le
  · rw [hstep]
    -- Adding `-x^(1)` sends the first double-dogleg iterate to the origin.
    ext i <;> fin_cases i <;>
      simp [chapter06Exercise62DoubleDoglegX1DeltaFiveQuartersPoint,
        chapter06Exercise62Origin, chapter06Exercise62Point]
      <;> ring_nf
