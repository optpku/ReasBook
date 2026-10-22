/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic

noncomputable section

open scoped Matrix

section

-- Semantic recall: `lean_leansearch` only surfaced the polynomial `newtonMap` API, so this
-- exercise is formalized as the concrete objective and parameter data that feed the local
-- Chapter 3 Newton and Newton-with-line-search owners.

local notation "Point" => EuclideanSpace ℝ (Fin 4)

/-- Convert an angle measured in degrees to radians. -/
private def degreesToRadians (θ : ℝ) : ℝ :=
  θ * Real.pi / 180

/-- The symmetric matrix `A` from the quartic Newton test problem. -/
def quarticNewtonTestMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(5 : ℝ), 1, 0, 1 / 2;
    1, 4, 1 / 2, 0;
    0, 1 / 2, 3, 0;
    1 / 2, 0, 0, 2]

/-- The quadratic form `xᵀ A x` attached to `quarticNewtonTestMatrix`. -/
def quarticNewtonTestQuadraticForm (x : Point) : ℝ :=
  inner ℝ x (quarticNewtonTestMatrix.toEuclideanLin x)

/-- Chapter03 Exercise 3.3: the objective
`f(x) = 1 / 2 * ‖x‖^2 + σ / 4 * (xᵀ A x)^2` on `ℝ⁴`, where
`A = quarticNewtonTestMatrix` and `xᵀ A x` is formalized as
`quarticNewtonTestQuadraticForm x`. -/
def quarticNewtonTestObjective (σ : ℝ) (x : Point) : ℝ :=
  (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) +
    (σ / 4) * (quarticNewtonTestQuadraticForm x) ^ (2 : ℕ)

/-- Expand `quarticNewtonTestObjective` into its defining quartic formula. -/
theorem quarticNewtonTestObjective_def (σ : ℝ) (x : Point) :
    quarticNewtonTestObjective σ x =
      (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) +
        (σ / 4) * (quarticNewtonTestQuadraticForm x) ^ (2 : ℕ) := rfl

/-- The case `σ = 1` from the exercise. -/
def quarticNewtonTestSigmaOne : ℝ :=
  1

/-- The case `σ = 10^4` from the exercise. -/
def quarticNewtonTestSigmaTenThousand : ℝ :=
  (10 : ℝ) ^ (4 : ℕ)

/-- The initial point `(cos 70°, sin 70°, cos 70°, sin 70°)`. -/
def quarticNewtonTestInitialPoint70 : Point :=
  !₂[Real.cos (degreesToRadians 70), Real.sin (degreesToRadians 70),
    Real.cos (degreesToRadians 70), Real.sin (degreesToRadians 70)]

/-- The initial point `(cos 50°, sin 50°, cos 50°, sin 50°)`. -/
def quarticNewtonTestInitialPoint50 : Point :=
  !₂[Real.cos (degreesToRadians 50), Real.sin (degreesToRadians 50),
    Real.cos (degreesToRadians 50), Real.sin (degreesToRadians 50)]

end
