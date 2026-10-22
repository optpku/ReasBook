/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_2_extra_1

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

-- Semantic recall: Chapter 10 already owns the Section 10.2 source penalty objective as
-- `problem.simplePenaltyObjective σ α`, so this lemma reuses that owner and adds only the
-- source-facing violation sublevel set needed for the constrained conclusion.

/-- The source violation sublevel set `‖c⁽-⁾(x)‖ ≤ δ`, written with an explicit violation map
`c⁽-⁾ : ℝ^n → ℝ^m`. -/
def simplePenaltyViolationSublevelSet
    (cNeg : Point → ConstraintPoint) (δ : ℝ) : Set Point :=
  {x | ‖cNeg x‖ ≤ δ}

/-- Membership in `simplePenaltyViolationSublevelSet cNeg δ` is exactly the source inequality
`‖c⁽-⁾(x)‖ ≤ δ`. -/
theorem mem_simplePenaltyViolationSublevelSet_iff
    (cNeg : Point → ConstraintPoint) (δ : ℝ) (x : Point) :
    x ∈ simplePenaltyViolationSublevelSet cNeg δ ↔ ‖cNeg x‖ ≤ δ :=
  Iff.rfl

namespace StandardPenaltyProblem

/-- Chapter10 Lemma 10.2.2: if `xσ` solves the simple penalty subproblem with objective
`problem.simplePenaltyObjective σ α` for a nonnegative penalty parameter `σ` and nonnegative
exponent `α`, then it also minimizes `problem.objective` on the violation sublevel set
`{x | ‖c⁽-⁾(x)‖ ≤ ‖c⁽-⁾(xσ)‖}`. -/
theorem isMinOnObjectiveOnSimplePenaltyViolationSublevelSet_of_isMinOn_simplePenaltyObjective
    (problem : StandardPenaltyProblem n m)
    {σ α : ℝ} (hσ : 0 ≤ σ) (hα : 0 ≤ α) (xσ : Point)
    (hxσ : IsMinOn (problem.simplePenaltyObjective σ α) Set.univ xσ) :
    IsMinOn
      problem.objective
      (simplePenaltyViolationSublevelSet
        problem.constraintViolation
        ‖problem.constraintViolation xσ‖)
      xσ := by
  refine isMinOn_iff.mpr ?_
  intro x hx
  have hpenalty := (isMinOn_iff.mp hxσ) x (by simp)
  have hviol : ‖problem.constraintViolation x‖ ≤ ‖problem.constraintViolation xσ‖ :=
    (mem_simplePenaltyViolationSublevelSet_iff
      problem.constraintViolation
      ‖problem.constraintViolation xσ‖
      x).mp hx
  have hrpow :
      Real.rpow ‖problem.constraintViolation x‖ α ≤
        Real.rpow ‖problem.constraintViolation xσ‖ α := by
    exact Real.rpow_le_rpow (norm_nonneg _) hviol hα
  have hscaled :
      σ * Real.rpow ‖problem.constraintViolation x‖ α ≤
        σ * Real.rpow ‖problem.constraintViolation xσ‖ α := by
    exact mul_le_mul_of_nonneg_left hrpow hσ
  have hobjective :
      problem.objective xσ ≤
        problem.objective x + σ * Real.rpow ‖problem.constraintViolation x‖ α -
          σ * Real.rpow ‖problem.constraintViolation xσ‖ α := by
    have hpenalty' :=
      sub_le_sub_right hpenalty (σ * Real.rpow ‖problem.constraintViolation xσ‖ α)
    rw [problem.simplePenaltyObjective_apply, problem.simplePenaltyObjective_apply] at hpenalty'
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hpenalty'
  have hcorrection :
      problem.objective x + σ * Real.rpow ‖problem.constraintViolation x‖ α -
          σ * Real.rpow ‖problem.constraintViolation xσ‖ α ≤
        problem.objective x := by
    have hnonpos :
        σ * Real.rpow ‖problem.constraintViolation x‖ α -
            σ * Real.rpow ‖problem.constraintViolation xσ‖ α ≤
          0 :=
      sub_nonpos.mpr hscaled
    have hadd := add_le_add_right hnonpos (problem.objective x)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd
  exact hobjective.trans hcorrection

end StandardPenaltyProblem
