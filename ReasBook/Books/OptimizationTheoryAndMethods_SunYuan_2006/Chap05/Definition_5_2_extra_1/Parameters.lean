/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

section

variable {n : ℕ}

-- Local declaration justification (source-local notation): the parameter formulas are stated on
-- one fixed Euclidean space `ℝ^n`, and the shorthand stays local to this item-owned module.
local notation "Point" => EuclideanSpace ℝ (Fin n)
-- Local declaration justification (source-local notation): the source parameter relation uses one
-- fixed real `n × n` matrix space, so the alias is kept local instead of becoming public API.
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- The scalar `μ = (yᵀ H y) * (sᵀ B s) / (sᵀ y)^2` from `(5.2.17)` used in the
inverse/Hessian-form Broyden parameter relation. -/
def broydenClassMu
    (H B : MatrixN) (s y : Point) : ℝ :=
  dotProduct y (H.mulVec y) * dotProduct s (B.mulVec s) / (dotProduct s y) ^ 2

/-- The defining scalar formula for `broydenClassMu`. -/
@[simp] theorem broydenClassMu_eq
    (H B : MatrixN) (s y : Point) :
    broydenClassMu H B s y =
      dotProduct y (H.mulVec y) * dotProduct s (B.mulVec s) / (dotProduct s y) ^ 2 := rfl

/-- The Hessian-form Broyden parameter `θ` corresponding to `φ` through `(5.2.16)`. -/
def broydenClassThetaParameter
    (H B : MatrixN) (s y : Point) (φ : ℝ) : ℝ :=
  (φ - 1) / (φ - 1 - φ * broydenClassMu H B s y)

/-- Expanding `broydenClassThetaParameter` gives the source relation
`θ = (φ - 1) / (φ - 1 - φ μ)` from `(5.2.16)`. -/
theorem broydenClassThetaParameter_eq
    (H B : MatrixN) (s y : Point) (φ : ℝ) :
    broydenClassThetaParameter H B s y φ =
      (φ - 1) / (φ - 1 - φ * broydenClassMu H B s y) := by
  rfl

end
