/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_2_extra_1

noncomputable section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Semantic recall: `Definition_5_2_extra_1` owns the Chapter 5 scalar `broydenClassMu`.
-- This file keeps only the degenerate-parameter bridge theorems attached to that owner.

/-- When `1 - broydenClassMu H B s y ≠ 0`, the denominator of the `φ ↔ θ` relation `(5.2.16)`
vanishes exactly at the degenerate parameter value `1 / (1 - μ)`. -/
theorem broydenClassThetaDenominator_eq_zero_iff
    (H B : MatrixN) (s y : Point) (φ : ℝ)
    (hμ : 1 - broydenClassMu H B s y ≠ 0) :
    φ - 1 - φ * broydenClassMu H B s y = 0 ↔
      φ = 1 / (1 - broydenClassMu H B s y) := by
  constructor
  · intro hφ
    apply (eq_div_iff hμ).2
    nlinarith [hφ]
  · intro hφ
    have hEq : φ * (1 - broydenClassMu H B s y) = 1 := by
      have := (eq_div_iff hμ).1 hφ
      simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc] using this
    nlinarith [hEq]

/-- Chapter05 Theorem 5.2.3: the degenerate value of the Broyden class update is
`1 / (1 - yᵀ H y * sᵀ B s / (sᵀ y)^2)`,
i.e. formula `(5.2.20)`. -/
theorem broydenClassDegenerateValue_eq_formula
    (H B : MatrixN) (s y : Point) :
    1 / (1 - broydenClassMu H B s y) =
      1 / (
        1 - dotProduct y (H.mulVec y) * dotProduct s (B.mulVec s) / (dotProduct s y) ^ 2
      ) := by
  simp [broydenClassMu]
