/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib
import Mathlib
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Theorem_6_1_11

noncomputable section

-- The exercise is a source-facing concrete double-dogleg computation, while Chapter 6 already
-- owns the reusable trust-region, Cauchy-point, and double-dogleg geometry through
-- `TrustRegionSubproblem`. This file therefore keeps the explicit exercise data and iterate
-- formula, but expresses the double-dogleg objects through those owner-level declarations.

local notation "Point" => EuclideanSpace ℝ (Fin 2)

open TrustRegionSubproblem

/-- The coordinate point `(a, b)ᵀ` in `EuclideanSpace ℝ (Fin 2)`. -/
def chapter06Exercise61Point (a b : ℝ) : Point :=
  a • (EuclideanSpace.basisFun (Fin 2) ℝ) 0 + b • (EuclideanSpace.basisFun (Fin 2) ℝ) 1

/-- The exercise objective `f(x) = x 0 ^ 4 + x 0 ^ 2 + x 1 ^ 2` on `ℝ²`. -/
def chapter06Exercise61Objective (x : Point) : ℝ :=
  x 0 ^ (4 : ℕ) + x 0 ^ (2 : ℕ) + x 1 ^ (2 : ℕ)

/-- The current iterate `x^(k) = (1, 1)ᵀ` from the exercise. -/
def chapter06Exercise61CurrentPoint : Point :=
  chapter06Exercise61Point 1 1

/-- Helper for Chapter06 Exercise 6.1: the squared norm of `chapter06Exercise61Point a b` is
`a^2 + b^2`. -/
theorem chapter06Exercise61Point_norm_sq (a b : ℝ) :
    ‖chapter06Exercise61Point a b‖ ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
  -- Rewrite the concrete coordinate point to the standard `ℝ²` norm-square formula.
  simpa [chapter06Exercise61Point] using
    (EuclideanSpace.real_norm_sq_eq (chapter06Exercise61Point a b))

/-- The trust-region radius `Δ_k = 1 / 2` from the exercise. -/
def chapter06Exercise61TrustRegionRadius : ℝ :=
  (1 : ℝ) / 2

/-- The Hessian approximation `B = diag(14, 2)` of the quadratic model at `x^(k)`. -/
def chapter06Exercise61HessianApprox : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![(14 : ℝ), 2]

/-- The exercise Hessian approximation is positive definite. -/
theorem chapter06Exercise61HessianApprox_posDef :
    chapter06Exercise61HessianApprox.PosDef := by
  simp [chapter06Exercise61HessianApprox]

/-- Helper for Chapter06 Exercise 6.1: the diagonal Hessian approximation is symmetric. -/
theorem chapter06Exercise61HessianApprox_isSymm :
    chapter06Exercise61HessianApprox.IsSymm := by
  -- Positive definiteness already packages the real-matrix symmetry needed by the subproblem.
  simpa [Matrix.isHermitian_iff_isSymm] using
    (show chapter06Exercise61HessianApprox.IsHermitian from chapter06Exercise61HessianApprox_posDef.1)

/-- The Chapter 6 double-dogleg interpolation factor
`γ = ‖g‖^4 / ((gᵀ B g) (gᵀ B⁻¹ g)) = 175 / 256` for the exercise data. -/
def chapter06Exercise61DoubleDoglegGamma : ℝ :=
  (175 : ℝ) / 256

/-- Helper for Chapter06 Exercise 6.1: the trust-region radius `1 / 2` is positive. -/
theorem chapter06Exercise61TrustRegionRadius_pos :
    0 < chapter06Exercise61TrustRegionRadius := by
  -- The concrete radius is a positive rational scalar.
  norm_num [chapter06Exercise61TrustRegionRadius]

/-- The concrete Chapter 6 trust-region subproblem determined by the exercise data. -/
def chapter06Exercise61Subproblem : TrustRegionSubproblem 2 where
  fAtCenter := chapter06Exercise61Objective chapter06Exercise61CurrentPoint
  gradient := chapter06Exercise61Point 6 2
  hessianApprox := chapter06Exercise61HessianApprox
  hessianApprox_symm := chapter06Exercise61HessianApprox_isSymm
  radius := chapter06Exercise61TrustRegionRadius
  radius_pos := chapter06Exercise61TrustRegionRadius_pos

/-- The exercise trust-region subproblem has a positive-definite Hessian approximation. -/
theorem chapter06Exercise61Subproblem_hessianApprox_posDef :
    chapter06Exercise61Subproblem.hessianApprox.PosDef := by
  -- The subproblem stores the same concrete Hessian approximation as the exercise data.
  simpa [chapter06Exercise61Subproblem] using chapter06Exercise61HessianApprox_posDef

/-- Helper for Chapter06 Exercise 6.1: the Newton step is `(-3 / 7, -1)ᵀ`. -/
theorem chapter06Exercise61Subproblem_newtonStep_eq :
    chapter06Exercise61Subproblem.newtonStep
        chapter06Exercise61Subproblem_hessianApprox_posDef.isUnit =
      chapter06Exercise61Point (-(3 : ℝ) / 7) (-1) := by
  -- Apply the concrete diagonal Hessian to the Newton step and solve the two scalar equations.
  let s :=
    chapter06Exercise61Subproblem.newtonStep
      chapter06Exercise61Subproblem_hessianApprox_posDef.isUnit
  have hmul :=
    chapter06Exercise61Subproblem.hessianApprox_mulVec_newtonStep_eq_neg_gradient
      chapter06Exercise61Subproblem_hessianApprox_posDef
  have h0 :
      s 0 =
        -(3 : ℝ) / 7 := by
    -- The first diagonal entry gives `14 * s₀ = -6`.
    have hcoord : 14 * s 0 = -6 := by
      simpa [s, chapter06Exercise61Subproblem, chapter06Exercise61Point, chapter06Exercise61HessianApprox,
        Matrix.mulVec, Fin.sum_univ_two] using congrFun hmul 0
    nlinarith
  have h1 :
      s 1 =
        -1 := by
    -- The second diagonal entry gives `2 * s₁ = -2`.
    have hcoord : 2 * s 1 = -2 := by
      simpa [s, chapter06Exercise61Subproblem, chapter06Exercise61Point, chapter06Exercise61HessianApprox,
        Matrix.mulVec, Fin.sum_univ_two] using congrFun hmul 1
    nlinarith
  ext i <;> fin_cases i
  · simpa [s, chapter06Exercise61Point] using h0
  · simpa [s, chapter06Exercise61Point] using h1

/-- For this exercise subproblem, the scalar `γ` computed from the canonical Chapter 6 formula is
`175 / 256`. -/
theorem chapter06Exercise61Subproblem_doubleDoglegGamma_eq :
    chapter06Exercise61Subproblem.doubleDoglegGamma
        chapter06Exercise61Subproblem_hessianApprox_posDef.isUnit =
      chapter06Exercise61DoubleDoglegGamma := by
  -- Evaluate the textbook formula using the explicit Newton step, norm square, and curvature.
  have hnorm_sq : ‖chapter06Exercise61Subproblem.gradient‖ ^ (2 : ℕ) = 40 := by
    calc
      ‖chapter06Exercise61Subproblem.gradient‖ ^ (2 : ℕ) =
          chapter06Exercise61Subproblem.gradient 0 ^ (2 : ℕ) +
            chapter06Exercise61Subproblem.gradient 1 ^ (2 : ℕ) := by
            simpa using (EuclideanSpace.real_norm_sq_eq chapter06Exercise61Subproblem.gradient)
      _ = 40 := by
        norm_num [chapter06Exercise61Subproblem, chapter06Exercise61Point]
  have hnorm_four : ‖chapter06Exercise61Subproblem.gradient‖ ^ (4 : ℕ) = 1600 := by
    nlinarith [hnorm_sq]
  have hcurv : chapter06Exercise61Subproblem.gradientCurvature = 512 := by
    -- The diagonal Hessian acts coordinatewise on the concrete gradient.
    norm_num [TrustRegionSubproblem.gradientCurvature, chapter06Exercise61Subproblem,
      chapter06Exercise61Point, chapter06Exercise61HessianApprox, dotProduct, Matrix.mulVec,
      Fin.sum_univ_two]
  have hnewton_dot :
      -dotProduct chapter06Exercise61Subproblem.gradient
          (chapter06Exercise61Subproblem.newtonStep
            chapter06Exercise61Subproblem_hessianApprox_posDef.isUnit) =
        (32 : ℝ) / 7 := by
    -- The Newton step closes the inverse-Hessian quadratic factor in the denominator.
    rw [chapter06Exercise61Subproblem_newtonStep_eq]
    norm_num [chapter06Exercise61Subproblem, chapter06Exercise61Point, dotProduct, Fin.sum_univ_two]
  rw [TrustRegionSubproblem.doubleDoglegGamma, hnorm_four, hcurv, hnewton_dot,
    chapter06Exercise61DoubleDoglegGamma]
  norm_num

/-- For this exercise subproblem, the Cauchy step is `(-15 / 32, -5 / 32)ᵀ`. -/
theorem chapter06Exercise61Subproblem_cauchyPoint_eq :
    chapter06Exercise61Subproblem.cauchyPoint =
      chapter06Exercise61Point (-(15 : ℝ) / 32) (-(5 : ℝ) / 32) := by
  -- The positive-curvature Cauchy formula reduces the step to a scalar multiple of the gradient.
  have hgrad : chapter06Exercise61Subproblem.gradient ≠ 0 := by
    intro hzero
    have hzero0 := congrArg (fun y : Point ↦ y 0) hzero
    norm_num [chapter06Exercise61Subproblem, chapter06Exercise61Point] at hzero0
  have hcurv_eq : chapter06Exercise61Subproblem.gradientCurvature = 512 := by
    norm_num [TrustRegionSubproblem.gradientCurvature, chapter06Exercise61Subproblem,
      chapter06Exercise61Point, chapter06Exercise61HessianApprox, dotProduct, Matrix.mulVec,
      Fin.sum_univ_two]
  have hcurv : 0 < chapter06Exercise61Subproblem.gradientCurvature := by
    rw [hcurv_eq]
    norm_num [TrustRegionSubproblem.gradientCurvature, chapter06Exercise61Subproblem,
      chapter06Exercise61Point, chapter06Exercise61HessianApprox, dotProduct, Matrix.mulVec,
      Fin.sum_univ_two]
  have hnorm_sq : ‖chapter06Exercise61Subproblem.gradient‖ ^ (2 : ℕ) = 40 := by
    simpa [chapter06Exercise61Subproblem] using
      show ‖chapter06Exercise61Point 6 2‖ ^ (2 : ℕ) = (40 : ℝ) by
        rw [chapter06Exercise61Point_norm_sq]
        norm_num
  have hnorm : ‖chapter06Exercise61Subproblem.gradient‖ = 2 * Real.sqrt 10 := by
    -- The concrete gradient `(6, 2)` has norm `sqrt 40 = 2 * sqrt 10`.
    have hnonneg : 0 ≤ ‖chapter06Exercise61Subproblem.gradient‖ := norm_nonneg _
    have hsqrt_nonneg : 0 ≤ 2 * Real.sqrt 10 := by
      positivity
    have hle : ‖chapter06Exercise61Subproblem.gradient‖ ≤ 2 * Real.sqrt 10 := by
      nlinarith [hnorm_sq, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by positivity)]
    have hge : 2 * Real.sqrt 10 ≤ ‖chapter06Exercise61Subproblem.gradient‖ := by
      nlinarith [hnorm_sq, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by positivity)]
    exact le_antisymm hle hge
  have hratio_le_one : (5 : ℝ) * Real.sqrt 10 / 16 ≤ 1 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (10 : ℝ) by positivity)]
  rw [TrustRegionSubproblem.cauchyPoint_eq_of_ne_zero _ hgrad]
  rw [TrustRegionSubproblem.cauchyPointScale_eq_min_of_pos_curvature _ hcurv]
  have hscalar :
      min
            (‖chapter06Exercise61Subproblem.gradient‖ ^ (3 : ℕ) /
              (chapter06Exercise61TrustRegionRadius *
                chapter06Exercise61Subproblem.gradientCurvature))
            1 *
          chapter06Exercise61TrustRegionRadius /
        ‖chapter06Exercise61Subproblem.gradient‖ =
      (5 : ℝ) / 64 := by
    rw [chapter06Exercise61TrustRegionRadius, hcurv_eq, hnorm]
    have hratio_eq :
        (2 * Real.sqrt 10) ^ (3 : ℕ) / (((1 : ℝ) / 2) * 512) =
          (5 : ℝ) * Real.sqrt 10 / 16 := by
      field_simp [Real.sqrt_ne_zero'.2 (show (0 : ℝ) < 10 by positivity)]
      rw [Real.sq_sqrt (show 0 ≤ (10 : ℝ) by positivity)]
      ring
    rw [hratio_eq, min_eq_left hratio_le_one]
    field_simp [Real.sqrt_ne_zero'.2 (show (0 : ℝ) < 10 by positivity)]
    norm_num
  ext i <;> fin_cases i
  · -- Evaluate the first coordinate of the explicit scalar multiple of the gradient.
    have hcoord :
        min
                (‖chapter06Exercise61Point 6 2‖ ^ (3 : ℕ) /
                  (chapter06Exercise61TrustRegionRadius *
                    chapter06Exercise61Subproblem.gradientCurvature))
                1 *
              chapter06Exercise61TrustRegionRadius /
            ‖chapter06Exercise61Point 6 2‖ *
          6 =
          (15 : ℝ) / 32 := by
      calc
        min
                (‖chapter06Exercise61Point 6 2‖ ^ (3 : ℕ) /
                  (chapter06Exercise61TrustRegionRadius *
                    chapter06Exercise61Subproblem.gradientCurvature))
                1 *
              chapter06Exercise61TrustRegionRadius /
            ‖chapter06Exercise61Point 6 2‖ *
          6 =
            ((5 : ℝ) / 64) * 6 := by
              rw [← hscalar]
              simp [chapter06Exercise61Subproblem]
        _ = (15 : ℝ) / 32 := by
          norm_num
    have hcoordNeg :
        -(min
                (‖chapter06Exercise61Point 6 2‖ ^ (3 : ℕ) /
                  (chapter06Exercise61TrustRegionRadius *
                    chapter06Exercise61Subproblem.gradientCurvature))
                1 *
              chapter06Exercise61TrustRegionRadius /
            ‖chapter06Exercise61Point 6 2‖ *
          6) =
          -(15 : ℝ) / 32 := by
      rw [hcoord]
      ring
    simpa [chapter06Exercise61Subproblem, chapter06Exercise61Point] using hcoordNeg
  · -- The second coordinate is the same scalar factor times the second gradient entry.
    have hcoord :
        min
                (‖chapter06Exercise61Point 6 2‖ ^ (3 : ℕ) /
                  (chapter06Exercise61TrustRegionRadius *
                    chapter06Exercise61Subproblem.gradientCurvature))
                1 *
              chapter06Exercise61TrustRegionRadius /
            ‖chapter06Exercise61Point 6 2‖ *
          2 =
          (5 : ℝ) / 32 := by
      calc
        min
                (‖chapter06Exercise61Point 6 2‖ ^ (3 : ℕ) /
                  (chapter06Exercise61TrustRegionRadius *
                    chapter06Exercise61Subproblem.gradientCurvature))
                1 *
              chapter06Exercise61TrustRegionRadius /
            ‖chapter06Exercise61Point 6 2‖ *
          2 =
            ((5 : ℝ) / 64) * 2 := by
              rw [← hscalar]
              simp [chapter06Exercise61Subproblem]
        _ = (5 : ℝ) / 32 := by
          norm_num
    have hcoordNeg :
        -(min
                (‖chapter06Exercise61Point 6 2‖ ^ (3 : ℕ) /
                  (chapter06Exercise61TrustRegionRadius *
                    chapter06Exercise61Subproblem.gradientCurvature))
                1 *
              chapter06Exercise61TrustRegionRadius /
            ‖chapter06Exercise61Point 6 2‖ *
          2) =
          -(5 : ℝ) / 32 := by
      rw [hcoord]
      ring
    simpa [chapter06Exercise61Subproblem, chapter06Exercise61Point] using hcoordNeg

/-- For this exercise data, the translated double-dogleg Cauchy point is
`(17 / 32, 27 / 32)ᵀ`. -/
theorem chapter06Exercise61DoubleDoglegCauchyPoint_eq :
    chapter06Exercise61CurrentPoint + chapter06Exercise61Subproblem.cauchyPoint =
      chapter06Exercise61Point ((17 : ℝ) / 32) ((27 : ℝ) / 32) := by
  -- Translate the explicit Cauchy step by the current iterate `(1, 1)`.
  rw [chapter06Exercise61Subproblem_cauchyPoint_eq]
  ext i <;> fin_cases i <;>
    simp [chapter06Exercise61CurrentPoint, chapter06Exercise61Point]
    <;> ring

/-- For this exercise data, the intermediate Newton point
`x^(k) + γ s^N` is `(1267 / 1792, 81 / 256)ᵀ`. -/
theorem chapter06Exercise61DoubleDoglegIntermediateNewtonPoint_eq :
    chapter06Exercise61CurrentPoint +
        chapter06Exercise61Subproblem.doubleDoglegIntermediateNewtonStep
          chapter06Exercise61Subproblem_hessianApprox_posDef.isUnit
          chapter06Exercise61DoubleDoglegGamma =
      chapter06Exercise61Point ((1267 : ℝ) / 1792) ((81 : ℝ) / 256) := by
  -- Rewrite the intermediate Newton point to `γ • sᴺ` and evaluate both coordinates.
  rw [TrustRegionSubproblem.doubleDoglegIntermediateNewtonStep,
    chapter06Exercise61Subproblem_newtonStep_eq, chapter06Exercise61DoubleDoglegGamma]
  ext i <;> fin_cases i <;>
    simp [chapter06Exercise61CurrentPoint, chapter06Exercise61Point]
    <;> ring

/-- The second-leg point on the double-dogleg path from the Cauchy point to the intermediate
Newton point with parameter `θ ∈ [0, 1]`. -/
def chapter06Exercise61DoubleDoglegSegmentPoint (θ : ℝ) : Point :=
  chapter06Exercise61CurrentPoint +
    chapter06Exercise61Subproblem.doubleDoglegPath
      chapter06Exercise61Subproblem_hessianApprox_posDef.isUnit
      chapter06Exercise61DoubleDoglegGamma
      (1 + θ)

/-- A point is the exercise's double-dogleg next iterate when the Cauchy point lies strictly
inside the trust region, the intermediate Newton point lies outside it, and the point is the
boundary point on the segment joining them. -/
def chapter06Exercise61IsDoubleDoglegNextIterate (xNext : Point) : Prop :=
  dist chapter06Exercise61CurrentPoint
      (chapter06Exercise61CurrentPoint + chapter06Exercise61Subproblem.cauchyPoint) <
    chapter06Exercise61Subproblem.radius ∧
  chapter06Exercise61Subproblem.radius <
      dist chapter06Exercise61CurrentPoint
        (chapter06Exercise61CurrentPoint +
          chapter06Exercise61Subproblem.doubleDoglegIntermediateNewtonStep
            chapter06Exercise61Subproblem_hessianApprox_posDef.isUnit
            chapter06Exercise61DoubleDoglegGamma) ∧
    ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      xNext = chapter06Exercise61DoubleDoglegSegmentPoint θ ∧
        dist chapter06Exercise61CurrentPoint xNext =
          chapter06Exercise61Subproblem.radius

/-- The explicit boundary point on the second double-dogleg segment:
`x^(k+1) = (17 / 32 + √15 / 160, 27 / 32 - 3 * √15 / 160)ᵀ`. -/
def chapter06Exercise61NextIterate : Point :=
  chapter06Exercise61Point
    ((17 : ℝ) / 32 + Real.sqrt 15 / 160)
    ((27 : ℝ) / 32 - (3 : ℝ) * Real.sqrt 15 / 160)

/-- Chapter06 Exercise 6.1: for
`f(x) = x 0 ^ 4 + x 0 ^ 2 + x 1 ^ 2`, current iterate `x^(k) = (1, 1)ᵀ`, and trust-region
radius `Δ_k = 1 / 2`, the double-dogleg method gives
`x^(k+1) = (17 / 32 + √15 / 160, 27 / 32 - 3 * √15 / 160)ᵀ`. -/
theorem chapter06Exercise61DoubleDoglegNextIterate :
    chapter06Exercise61IsDoubleDoglegNextIterate chapter06Exercise61NextIterate := by
  -- Route correction: the proof closes by concrete radius computations on the second dogleg leg,
  -- not by re-solving the subproblem abstractly.
  have hcauchy_dist :
      dist chapter06Exercise61CurrentPoint
          (chapter06Exercise61CurrentPoint + chapter06Exercise61Subproblem.cauchyPoint) =
        ‖chapter06Exercise61Subproblem.cauchyPoint‖ := by
    -- Translation invariance reduces the first distance to the norm of the Cauchy step.
    rw [dist_eq_norm]
    simp
  have hcauchy_norm_sq :
      ‖chapter06Exercise61Subproblem.cauchyPoint‖ ^ (2 : ℕ) = (125 : ℝ) / 512 := by
    -- Evaluate the concrete Cauchy step in coordinates.
    rw [chapter06Exercise61Subproblem_cauchyPoint_eq, chapter06Exercise61Point_norm_sq]
    ring_nf
  have hcauchy_inside :
      dist chapter06Exercise61CurrentPoint
          (chapter06Exercise61CurrentPoint + chapter06Exercise61Subproblem.cauchyPoint) <
        chapter06Exercise61Subproblem.radius := by
    -- Compare the exact squared norm `125/1024` with the trust-region radius square `1/4`.
    have hsq_lt : (125 : ℝ) / 512 < ((1 : ℝ) / 2) ^ (2 : ℕ) := by
      norm_num
    have hlt : ‖chapter06Exercise61Subproblem.cauchyPoint‖ < (1 : ℝ) / 2 := by
      nlinarith [hcauchy_norm_sq, hsq_lt, norm_nonneg chapter06Exercise61Subproblem.cauchyPoint]
    simpa [chapter06Exercise61TrustRegionRadius, chapter06Exercise61Subproblem, hcauchy_dist] using
      hlt
  have hintermediate_dist :
      dist chapter06Exercise61CurrentPoint
          (chapter06Exercise61CurrentPoint +
            chapter06Exercise61Subproblem.doubleDoglegIntermediateNewtonStep
              chapter06Exercise61Subproblem_hessianApprox_posDef.isUnit
              chapter06Exercise61DoubleDoglegGamma) =
        ‖chapter06Exercise61Subproblem.doubleDoglegIntermediateNewtonStep
            chapter06Exercise61Subproblem_hessianApprox_posDef.isUnit
            chapter06Exercise61DoubleDoglegGamma‖ := by
    -- The same translation argument reduces the second distance to the step norm.
    rw [dist_eq_norm]
    simp
  have hintermediate_norm_sq :
      ‖chapter06Exercise61Subproblem.doubleDoglegIntermediateNewtonStep
          chapter06Exercise61Subproblem_hessianApprox_posDef.isUnit
          chapter06Exercise61DoubleDoglegGamma‖ ^ (2 : ℕ) =
        (18125 : ℝ) / 32768 := by
    -- Expand `γ sᴺ` in coordinates and compute its squared norm exactly.
    rw [TrustRegionSubproblem.doubleDoglegIntermediateNewtonStep,
      chapter06Exercise61Subproblem_newtonStep_eq, chapter06Exercise61DoubleDoglegGamma,
      norm_smul, Real.norm_of_nonneg (by positivity)]
    have hnewton_norm_sq :
        ‖chapter06Exercise61Point (-(3 : ℝ) / 7) (-1)‖ ^ (2 : ℕ) = (58 : ℝ) / 49 := by
      rw [chapter06Exercise61Point_norm_sq]
      norm_num
    nlinarith [hnewton_norm_sq, norm_nonneg (chapter06Exercise61Point (-(3 : ℝ) / 7) (-1))]
  have hintermediate_outside :
      chapter06Exercise61Subproblem.radius <
        dist chapter06Exercise61CurrentPoint
          (chapter06Exercise61CurrentPoint +
            chapter06Exercise61Subproblem.doubleDoglegIntermediateNewtonStep
              chapter06Exercise61Subproblem_hessianApprox_posDef.isUnit
              chapter06Exercise61DoubleDoglegGamma) := by
    -- The intermediate Newton point lies outside because `18125/32768 > 1/4`.
    have hsq_lt : ((1 : ℝ) / 2) ^ (2 : ℕ) < (18125 : ℝ) / 32768 := by
      norm_num
    have hlt :
        (1 : ℝ) / 2 <
          ‖chapter06Exercise61Subproblem.doubleDoglegIntermediateNewtonStep
              chapter06Exercise61Subproblem_hessianApprox_posDef.isUnit
              chapter06Exercise61DoubleDoglegGamma‖ := by
      nlinarith [hintermediate_norm_sq,
        hsq_lt,
        norm_nonneg
          (chapter06Exercise61Subproblem.doubleDoglegIntermediateNewtonStep
            chapter06Exercise61Subproblem_hessianApprox_posDef.isUnit
            chapter06Exercise61DoubleDoglegGamma)]
    simpa [chapter06Exercise61TrustRegionRadius, chapter06Exercise61Subproblem,
      hintermediate_dist] using hlt
  let θ : ℝ := 8 * Real.sqrt 15 / 225
  have hθ_nonneg : 0 ≤ θ := by
    -- The chosen second-leg parameter is a nonnegative multiple of `sqrt 15`.
    dsimp [θ]
    positivity
  have hθ_pos : 0 < θ := by
    -- This witness is strictly positive, so the path is genuinely on the second leg.
    dsimp [θ]
    positivity
  have hθ_le_one : θ ≤ 1 := by
    -- Squaring shows `8 * sqrt 15 / 225 ≤ 1`.
    dsimp [θ]
    nlinarith [Real.sq_sqrt (show 0 ≤ (15 : ℝ) by positivity)]
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) 1 := by
    -- Package the witness bounds for the existential clause.
    exact ⟨hθ_nonneg, hθ_le_one⟩
  have hsegment_eq :
      chapter06Exercise61DoubleDoglegSegmentPoint θ = chapter06Exercise61NextIterate := by
    -- Move to the second dogleg branch and evaluate the affine interpolation in coordinates.
    rw [chapter06Exercise61DoubleDoglegSegmentPoint]
    rw [TrustRegionSubproblem.doubleDoglegPath_eq_cauchyPoint_add_smul_of_one_lt_of_le_two
      _ _ _ _ (by linarith [hθ_pos]) (by linarith [hθ_le_one])]
    rw [chapter06Exercise61Subproblem_cauchyPoint_eq,
      TrustRegionSubproblem.doubleDoglegIntermediateNewtonStep,
      chapter06Exercise61Subproblem_newtonStep_eq, chapter06Exercise61DoubleDoglegGamma]
    ext i <;> fin_cases i
    · -- The first coordinate lands at `17/32 + sqrt 15 / 160`.
      simp [chapter06Exercise61CurrentPoint, chapter06Exercise61NextIterate,
        chapter06Exercise61Point, θ]
      field_simp [Real.sqrt_ne_zero'.2 (show (0 : ℝ) < 15 by positivity)]
      ring
    · -- The second coordinate lands at `27/32 - 3 * sqrt 15 / 160`.
      simp [chapter06Exercise61CurrentPoint, chapter06Exercise61NextIterate,
        chapter06Exercise61Point, θ]
      field_simp [Real.sqrt_ne_zero'.2 (show (0 : ℝ) < 15 by positivity)]
      ring
  have hnext_diff :
      chapter06Exercise61CurrentPoint - chapter06Exercise61NextIterate =
        chapter06Exercise61Point
          ((15 : ℝ) / 32 - Real.sqrt 15 / 160)
          ((5 : ℝ) / 32 + (3 : ℝ) * Real.sqrt 15 / 160) := by
    -- Normalize the final iterate displacement to a concrete coordinate vector.
    ext i <;> fin_cases i <;>
      simp [chapter06Exercise61CurrentPoint, chapter06Exercise61NextIterate,
        chapter06Exercise61Point]
      <;> ring
  have hnext_boundary :
      dist chapter06Exercise61CurrentPoint chapter06Exercise61NextIterate =
        chapter06Exercise61Subproblem.radius := by
    -- The explicit iterate lies on the trust-region boundary because its squared displacement is
    -- exactly `1/4`.
    rw [dist_eq_norm, hnext_diff]
    have hsqrt : Real.sqrt 15 ^ (2 : ℕ) = 15 := by
      rw [Real.sq_sqrt (show 0 ≤ (15 : ℝ) by positivity)]
    have hnext_norm_sq :
        ‖chapter06Exercise61Point
            ((15 : ℝ) / 32 - Real.sqrt 15 / 160)
            ((5 : ℝ) / 32 + (3 : ℝ) * Real.sqrt 15 / 160)‖ ^ (2 : ℕ) =
          (1 : ℝ) / 4 := by
      rw [chapter06Exercise61Point_norm_sq]
      nlinarith [hsqrt]
    have hnorm :
        ‖chapter06Exercise61Point
            ((15 : ℝ) / 32 - Real.sqrt 15 / 160)
            ((5 : ℝ) / 32 + (3 : ℝ) * Real.sqrt 15 / 160)‖ =
          (1 : ℝ) / 2 := by
      nlinarith [hnext_norm_sq,
        norm_nonneg
          (chapter06Exercise61Point
            ((15 : ℝ) / 32 - Real.sqrt 15 / 160)
            ((5 : ℝ) / 32 + (3 : ℝ) * Real.sqrt 15 / 160))]
    simpa [chapter06Exercise61TrustRegionRadius, chapter06Exercise61Subproblem] using hnorm
  refine ⟨hcauchy_inside, hintermediate_outside, θ, hθ_mem, ?_, hnext_boundary⟩
  -- The explicit iterate is exactly the second-leg boundary point selected above.
  symm
  exact hsegment_eq
