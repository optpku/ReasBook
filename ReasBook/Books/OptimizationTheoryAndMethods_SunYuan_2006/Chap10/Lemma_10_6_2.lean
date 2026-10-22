/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_6_extra_1

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

-- Domain sampling:
-- * `StandardPenaltyProblem` from `Definition_10_1_extra_1` is the chapter's source-facing owner
--   for mixed equality/inequality constrained problems.
-- * `StandardPenaltyProblem.nonsmoothExactPenalty` from `Definition_10_6_extra_1` is the
--   source-facing owner for the nonsmooth exact penalty `x ↦ f(x) + σ * h(c⁽-⁾(x))`.
-- * Section 10.2's local notation `P_σ` in `Lemma_10_2_1` is the chapter's notation precedent
--   for repeated penalty-stage objectives once the ambient problem data are fixed.
-- * `PenaltyFunction.nonsmoothExact` remains the bundled bridge/view once `σ > 0` is used to
--   package that objective as a `PenaltyFunction`.
-- * `IsMinOn` is the canonical mathlib minimizer predicate.
-- This lemma is therefore source-facing theorem API built on the existing exact-penalty owner,
-- not a second local penalty-object definition.

variable (problem : StandardPenaltyProblem n m)

/-- Helper for Chapter10 Lemma 10.6.2: the exact-penalty kernel value
`h (c⁽-⁾[problem] (x σ))` is antitone along global minimizers of the nonsmooth exact-penalty
subproblems. -/
lemma nonsmooth_exact_penalty_kernel_value_antitone
    (h : ConstraintPoint → ℝ) (x : ℝ → Point)
    (hx : ∀ {σ : ℝ}, 0 < σ → IsMinOn (problem.nonsmoothExactPenalty h σ) Set.univ (x σ))
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) :
    h (c⁽-⁾[problem] (x σ₂)) ≤
      h (c⁽-⁾[problem] (x σ₁)) := by
  have hσ₂ : 0 < σ₂ := lt_trans hσ₁ hσ₁₂
  -- Compare each stage minimizer against the point selected by the other stage.
  have hmin₁₂ :
      problem.nonsmoothExactPenalty h σ₁ (x σ₁) ≤
        problem.nonsmoothExactPenalty h σ₁ (x σ₂) :=
    (isMinOn_iff.mp (hx (σ := σ₁) hσ₁)) (x σ₂) (by simp)
  have hmin₂₁ :
      problem.nonsmoothExactPenalty h σ₂ (x σ₂) ≤
        problem.nonsmoothExactPenalty h σ₂ (x σ₁) :=
    (isMinOn_iff.mp (hx (σ := σ₂) hσ₂)) (x σ₁) (by simp)
  set f₁ : ℝ := problem.objective (x σ₁)
  set f₂ : ℝ := problem.objective (x σ₂)
  set v₁ : ℝ := h (c⁽-⁾[problem] (x σ₁))
  set v₂ : ℝ := h (c⁽-⁾[problem] (x σ₂))
  -- Normalize both inequalities to the shared `f + σ * v` shape from the source proof.
  have hmin₁₂' : f₁ + σ₁ * v₁ ≤ f₂ + σ₁ * v₂ := by
    simpa [f₁, f₂, v₁, v₂, problem.nonsmoothExactPenalty_apply] using hmin₁₂
  have hmin₂₁' : f₂ + σ₂ * v₂ ≤ f₁ + σ₂ * v₁ := by
    simpa [f₁, f₂, v₁, v₂, problem.nonsmoothExactPenalty_apply] using hmin₂₁
  -- Subtracting the normalized inequalities isolates the kernel values.
  nlinarith

/-- Chapter10 Lemma 10.6.2 (1): if `0 < σ₁ < σ₂` and `x σ` globally minimizes the chapter's
source exact-penalty objective `problem.nonsmoothExactPenalty h σ` for every positive `σ`, then
`f (x σ₂) ≥ f (x σ₁)`. -/
theorem nonsmoothExactPenaltyObjectiveValueMono
    (h : ConstraintPoint → ℝ) (x : ℝ → Point)
    (hx : ∀ {σ : ℝ}, 0 < σ → IsMinOn (problem.nonsmoothExactPenalty h σ) Set.univ (x σ))
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) :
    problem.objective (x σ₂) ≥ problem.objective (x σ₁) := by
  have hmin₁₂ :
      problem.nonsmoothExactPenalty h σ₁ (x σ₁) ≤
        problem.nonsmoothExactPenalty h σ₁ (x σ₂) :=
    (isMinOn_iff.mp (hx (σ := σ₁) hσ₁)) (x σ₂) (by simp)
  have hkernel :=
    nonsmooth_exact_penalty_kernel_value_antitone
      (problem := problem) (h := h) (x := x) (hx := hx) hσ₁ hσ₁₂
  set f₁ : ℝ := problem.objective (x σ₁)
  set f₂ : ℝ := problem.objective (x σ₂)
  set t₁ : ℝ := σ₁ * h (c⁽-⁾[problem] (x σ₁))
  set t₂ : ℝ := σ₁ * h (c⁽-⁾[problem] (x σ₂))
  -- Rewrite the `σ₁`-stage minimizer comparison into a common objective-plus-penalty form.
  have hmin₁₂' : f₁ + t₁ ≤ f₂ + t₂ := by
    simpa [f₁, f₂, t₁, t₂, problem.nonsmoothExactPenalty_apply] using hmin₁₂
  -- Scale the kernel comparison by the nonnegative parameter `σ₁`.
  have hscaled : t₂ ≤ t₁ := by
    simpa [t₁, t₂] using mul_le_mul_of_nonneg_left hkernel hσ₁.le
  -- Cancelling the common `σ₁`-weighted penalty term yields monotonicity of the objective.
  linarith

/-- Chapter10 Lemma 10.6.2 (2): under the same nonsmooth exact-penalty minimizer hypotheses,
`h (c⁽-⁾(x σ₂)) ≤ h (c⁽-⁾(x σ₁))` whenever `0 < σ₁ < σ₂`. -/
theorem nonsmoothExactPenaltyTermValueAntitone
    (h : ConstraintPoint → ℝ) (x : ℝ → Point)
    (hx : ∀ {σ : ℝ}, 0 < σ → IsMinOn (problem.nonsmoothExactPenalty h σ) Set.univ (x σ))
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) :
    h (c⁽-⁾[problem] (x σ₂)) ≤
      h (c⁽-⁾[problem] (x σ₁)) := by
  -- This is exactly the kernel comparison established in the helper lemma.
  simpa using
    nonsmooth_exact_penalty_kernel_value_antitone
      (problem := problem) (h := h) (x := x) (hx := hx) hσ₁ hσ₁₂

#print axioms nonsmoothExactPenaltyObjectiveValueMono
#print axioms nonsmoothExactPenaltyTermValueAntitone

end
