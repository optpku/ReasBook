/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_1_extra_1
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Filter

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

-- Domain sampling:
-- * primary domain: Chapter 10 simple penalty functions for `StandardPenaltyProblem`.
-- * inspected chapter/project owners of the same kind:
--   `StandardPenaltyProblem.constraintViolation` and `PenaltyFunction` in
--   `Definition_10_1_extra_1`,
--   `PenaltyFunction.quadratic` there as the existing bundled penalty constructor for the same
--   owner,
--   `StandardPenaltyProblem.nonsmoothExactPenalty` and `PenaltyFunction.nonsmoothExact` in
--   `Definition_10_6_extra_1` as the same source-facing/bridge split in a later section.
-- * best owner abstraction: the Section 10.2 stage objective belongs to
--   `StandardPenaltyProblem`; `PenaltyFunction.simple` is the bundled bridge/view under the
--   positivity hypotheses.
-- * primitive data vs. derived API:
--   primitive data are the constrained problem, the penalty parameter `σ`, and the exponent `α`;
--   the bundled `PenaltyFunction.simple` object is derived from that source-facing owner.

namespace StandardPenaltyProblem

/-- Source-facing layer for Chapter10 Definition 10.2-extra-1: for a fixed problem and exponent
`α`, the Section 10.2 family `P_σ` is the stage objective
`x ↦ f(x) + σ * ‖c⁽-⁾[problem] x‖^α`. -/
def simplePenaltyObjective
    (problem : StandardPenaltyProblem n m) (σ α : ℝ) : Point → ℝ :=
  fun x ↦ problem.objective x + σ * Real.rpow ‖c⁽-⁾[problem] x‖ α

section

variable (problem : StandardPenaltyProblem n m) (α : ℝ)

/-- With `problem` and `α` fixed, the Section 10.2 stage objective is written `P_σ`. -/
local notation:max "P_" σ => problem.simplePenaltyObjective σ α

/-- Evaluating `P_σ` unfolds to the textbook Section 10.2 formula
`P_σ(x) = f(x) + σ * ‖c⁽-⁾[problem] x‖^α`. -/
@[simp] theorem simplePenaltyObjective_apply
    (σ : ℝ) (x : Point) :
    (P_ σ : Point → ℝ) x =
      problem.objective x + σ * Real.rpow ‖c⁽-⁾[problem] x‖ α :=
  rfl

end

end StandardPenaltyProblem

namespace PenaltyFunction

/-- The Section 10.2 power penalty term `c ↦ σ * ‖c‖^α` vanishes at `0` when `α > 0`. -/
theorem simplePenaltyTerm_zero (σ α : ℝ) (hα : 0 < α) :
    (fun c : ConstraintPoint ↦ σ * Real.rpow ‖c‖ α) 0 = 0 := by
  simp [Real.zero_rpow hα.ne']

/-- Chapter10 Definition 10.2-extra-1: for positive `σ` and `α`, the Section 10.2 power
penalty term tends to `+∞` along the cocompact filter on `ℝ^m`. -/
theorem simplePenaltyTerm_tendsto_atTop (σ α : ℝ) (hσ : 0 < σ) (hα : 0 < α) :
    Tendsto (fun c : ConstraintPoint ↦ σ * Real.rpow ‖c‖ α)
      (cocompact ConstraintPoint) atTop := by
  -- First, cocompact escape in `ConstraintPoint` forces the norm to diverge to `+∞`.
  have hnorm :
      Tendsto (fun c : ConstraintPoint ↦ ‖c‖) (cocompact ConstraintPoint) atTop := by
    simpa [dist_eq_norm] using
      (tendsto_dist_right_cocompact_atTop (0 : ConstraintPoint))
  -- Then positive real powers preserve `atTop`, so `‖c‖^α` also diverges.
  have hrpowComp :
      Tendsto (((fun x : ℝ ↦ x ^ α) ∘ fun c : ConstraintPoint ↦ ‖c‖))
        (cocompact ConstraintPoint) atTop := by
    exact (tendsto_rpow_atTop hα).comp hnorm
  have hrpow :
      Tendsto (fun c : ConstraintPoint ↦ ‖c‖ ^ α)
        (cocompact ConstraintPoint) atTop := by
    refine hrpowComp.congr' ?_
    filter_upwards with c
    rfl
  -- Finally, multiplying by the positive penalty parameter `σ` keeps the limit at `+∞`.
  simpa only [Real.rpow_eq_pow] using Tendsto.const_mul_atTop hσ hrpow

/-- Helper for Chapter10 Definition 10.2-extra-1: for a fixed constrained problem, positive
exponent `α`, and positive penalty parameter `σ`, the simple penalty function is the
`PenaltyFunction` with term `c ↦ σ * ‖c‖^α`. -/
def simple (problem : StandardPenaltyProblem n m) (α : ℝ) (hα : 0 < α) (σ : ℝ) (hσ : 0 < σ) :
    PenaltyFunction problem where
  penaltyTerm := fun c ↦ σ * Real.rpow ‖c‖ α
  penaltyTerm_zero := simplePenaltyTerm_zero σ α hα
  penaltyTerm_tendsto_atTop := simplePenaltyTerm_tendsto_atTop σ α hσ hα

/-- Evaluating `PenaltyFunction.simple problem α hα σ hσ` recovers the source-facing Section
10.2 objective `problem.simplePenaltyObjective σ α`. -/
@[simp] theorem simple_apply
    (problem : StandardPenaltyProblem n m) (α : ℝ) (hα : 0 < α) (σ : ℝ) (hσ : 0 < σ)
    (x : Point) :
    simple problem α hα σ hσ x = problem.simplePenaltyObjective σ α x :=
  rfl

end PenaltyFunction

namespace StandardPenaltyProblem

section

variable (problem : StandardPenaltyProblem n m) (α : ℝ)

/-- With `problem` and `α` fixed, the Section 10.2 stage objective is written `P_σ`. -/
local notation:max "P_" σ => problem.simplePenaltyObjective σ α

/-- Under the positivity hypotheses from Section 10.2, the source-facing objective view
`P_σ` is exactly the evaluation of the canonical owner
`PenaltyFunction.simple problem α hα σ hσ`. -/
theorem simplePenaltyObjective_eq_simple
    (hα : 0 < α) (σ : ℝ) (hσ : 0 < σ) :
    (P_ σ : Point → ℝ) = PenaltyFunction.simple problem α hα σ hσ :=
  rfl

end

end StandardPenaltyProblem

end
