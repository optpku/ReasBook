/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_2_extra_1

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Semantic recall: Section 10.2's source-facing family is the local notation `P_ σ` for
-- `problem.simplePenaltyObjective σ α`, while `PenaltyFunction.simple` remains the canonical
-- owner underneath and `IsMinOn` is the canonical global-minimizer API.

section

variable (problem : StandardPenaltyProblem n m) {α : ℝ}

local notation:max "P_" σ => problem.simplePenaltyObjective σ α

/-- Chapter10 Lemma 10.2.1 (1): if `0 < σ₁ < σ₂` and `x σ` globally minimizes `P_σ` for every
positive `σ`, with fixed exponent `α`, then `P_(σ₁)(x σ₁) ≤ P_(σ₂)(x σ₂)`. -/
theorem simplePenaltyMinValueMono
    (x : ℝ → Point)
    (hx : ∀ {σ : ℝ}, 0 < σ → IsMinOn (P_ σ) Set.univ (x σ))
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) :
    (P_ σ₁) (x σ₁) ≤ (P_ σ₂) (x σ₂) := by
  -- Compare the `σ₁`-stage minimizer against the competitor `x σ₂`.
  have hmin₁₂ : (P_ σ₁) (x σ₁) ≤ (P_ σ₁) (x σ₂) :=
    (isMinOn_iff.mp (hx (σ := σ₁) hσ₁)) (x σ₂) (by simp)
  -- The penalty term at `x σ₂` grows monotonically with the parameter `σ`.
  have hpenalty₂ :
      σ₁ * Real.rpow ‖problem.constraintViolation (x σ₂)‖ α ≤
        σ₂ * Real.rpow ‖problem.constraintViolation (x σ₂)‖ α := by
    have hnonneg :
        0 ≤ Real.rpow ‖problem.constraintViolation (x σ₂)‖ α :=
      Real.rpow_nonneg (norm_nonneg _) _
    exact mul_le_mul_of_nonneg_right hσ₁₂.le hnonneg
  calc
    (P_ σ₁) (x σ₁) ≤ (P_ σ₁) (x σ₂) := hmin₁₂
    _ = problem.objective (x σ₂) +
          σ₁ * Real.rpow ‖problem.constraintViolation (x σ₂)‖ α := by
          rw [problem.simplePenaltyObjective_apply]
    _ ≤ problem.objective (x σ₂) +
          σ₂ * Real.rpow ‖problem.constraintViolation (x σ₂)‖ α :=
      add_le_add_right hpenalty₂ _
    _ = (P_ σ₂) (x σ₂) := by
      rw [problem.simplePenaltyObjective_apply]

/-- Helper for Chapter10 Lemma 10.2.1: the powered violation term
`‖c⁽-⁾(x σ)‖^α` is antitone along global minimizers of the simple penalty subproblems. -/
lemma simplePenaltyViolationPowerAntitone
    (x : ℝ → Point)
    (hx : ∀ {σ : ℝ}, 0 < σ → IsMinOn (P_ σ) Set.univ (x σ))
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) :
    Real.rpow ‖problem.constraintViolation (x σ₂)‖ α ≤
      Real.rpow ‖problem.constraintViolation (x σ₁)‖ α := by
  have hσ₂ : 0 < σ₂ := lt_trans hσ₁ hσ₁₂
  -- Evaluate each stage minimizer at the other stage's point to obtain the two cross inequalities.
  have hmin₁₂ : (P_ σ₁) (x σ₁) ≤ (P_ σ₁) (x σ₂) :=
    (isMinOn_iff.mp (hx (σ := σ₁) hσ₁)) (x σ₂) (by simp)
  have hmin₂₁ : (P_ σ₂) (x σ₂) ≤ (P_ σ₂) (x σ₁) :=
    (isMinOn_iff.mp (hx (σ := σ₂) hσ₂)) (x σ₁) (by simp)
  set f₁ : ℝ := problem.objective (x σ₁)
  set f₂ : ℝ := problem.objective (x σ₂)
  set v₁ : ℝ := Real.rpow ‖problem.constraintViolation (x σ₁)‖ α
  set v₂ : ℝ := Real.rpow ‖problem.constraintViolation (x σ₂)‖ α
  -- Normalize both inequalities to the common `f + σ * v` shape from the source proof.
  have hmin₁₂' : f₁ + σ₁ * v₁ ≤ f₂ + σ₁ * v₂ := by
    simpa [f₁, f₂, v₁, v₂, problem.simplePenaltyObjective_apply] using hmin₁₂
  have hmin₂₁' : f₂ + σ₂ * v₂ ≤ f₁ + σ₂ * v₁ := by
    simpa [f₁, f₂, v₁, v₂, problem.simplePenaltyObjective_apply] using hmin₂₁
  -- Subtracting the two normalized inequalities isolates the violation terms.
  nlinarith

/-- Chapter10 Lemma 10.2.1 (2): under the same simple-penalty setup with fixed exponent `α`,
`problem.objective (x σ₁) ≤ problem.objective (x σ₂)` whenever `0 < σ₁ < σ₂`. -/
theorem simplePenaltyObjectiveValueMono
    (x : ℝ → Point)
    (hx : ∀ {σ : ℝ}, 0 < σ → IsMinOn (P_ σ) Set.univ (x σ))
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) :
    problem.objective (x σ₁) ≤ problem.objective (x σ₂) := by
  have hmin₁₂ : (P_ σ₁) (x σ₁) ≤ (P_ σ₁) (x σ₂) :=
    (isMinOn_iff.mp (hx (σ := σ₁) hσ₁)) (x σ₂) (by simp)
  have hviol :=
    simplePenaltyViolationPowerAntitone
      (problem := problem) (x := x) (hx := hx) hσ₁ hσ₁₂
  set f₁ : ℝ := problem.objective (x σ₁)
  set f₂ : ℝ := problem.objective (x σ₂)
  set t₁ : ℝ := σ₁ * Real.rpow ‖problem.constraintViolation (x σ₁)‖ α
  set t₂ : ℝ := σ₁ * Real.rpow ‖problem.constraintViolation (x σ₂)‖ α
  -- Rewrite the minimizer inequality at the common parameter `σ₁`.
  have hmin₁₂' : f₁ + t₁ ≤ f₂ + t₂ := by
    simpa [f₁, f₂, t₁, t₂, problem.simplePenaltyObjective_apply] using hmin₁₂
  -- Scale the powered-violation comparison by the nonnegative factor `σ₁`.
  have hscaled : t₂ ≤ t₁ := by
    simpa [t₁, t₂] using mul_le_mul_of_nonneg_left hviol hσ₁.le
  -- Cancel the common penalty contribution to recover monotonicity of the objective values.
  linarith

/-- Chapter10 Lemma 10.2.1 (3): under the same simple-penalty setup with fixed `α > 0`,
the source violation norm `‖c⁽-⁾(x σ)‖` is antitone in `σ` for `0 < σ₁ < σ₂`. -/
theorem simplePenaltyViolationNormAntitone
    (x : ℝ → Point)
    (hx : ∀ {σ : ℝ}, 0 < σ → IsMinOn (P_ σ) Set.univ (x σ))
    (hα : 0 < α) {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) :
    ‖problem.constraintViolation (x σ₂)‖ ≤ ‖problem.constraintViolation (x σ₁)‖ := by
  have hviol :=
    simplePenaltyViolationPowerAntitone
      (problem := problem) (x := x) (hx := hx) hσ₁ hσ₁₂
  -- Invert the positive power once, after the comparison has been normalized.
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hα).mp hviol

end
