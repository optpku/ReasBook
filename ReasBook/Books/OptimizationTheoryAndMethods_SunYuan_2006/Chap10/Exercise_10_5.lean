/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Lemma_10_3_1

noncomputable section

section

open scoped BigOperators

variable {Point : Type*} {ι : Type*} [Fintype ι]

-- Domain sampling:
-- * primary domain: Chapter 10 interior-point penalty problems
-- * inspected owner declarations in this domain:
--   `InteriorPointPenaltyProblem`,
--   `InteriorPointPenaltyProblem.penaltyFunction_apply`,
--   `InteriorPointPenaltyProblem.HasPositiveBarrierValues`,
--   `InteriorPointPenaltyProblem.penaltyValue_antitone`,
--   `InteriorPointPenaltyProblem.objective_antitone`,
--   `InteriorPointPenaltyProblem.barrierSum_monotone`
-- * best owner abstraction: `InteriorPointPenaltyProblem Point ι`
-- * source-facing layer here: the exercise penalty sums with the pointwise reciprocal
--   `1 / constraint i x`
-- * core/canonical layer here: owner-level minimizer monotonicity statements for
--   `problem.penaltyFunction σ` on `problem.strictFeasibleSet`
-- * bridge/view layer here: a private bundled `InteriorPointPenaltyProblem` using the
--   reciprocal barrier, only to reuse the chapter owner lemmas
-- Primitive data here is only the objective, the inequality constraints, and the nonempty
-- strict feasible region. The strict-feasible set, barrier sum, penalty function, and monotonicity
-- API are derived from the owner and are not stored again locally. The source-facing minimizer
-- hypothesis below records both strict-feasible membership and `IsMinOn`, since the mathlib
-- minimizer predicate alone does not imply membership in the minimizing set.

private theorem one_div_large_near_zero :
    ∀ R : ℝ, ∃ δ > 0, ∀ ⦃c : ℝ⦄, 0 < c → c < δ → R < 1 / c := by
  intro R
  refine ⟨1 / (max R 0 + 1), one_div_pos.mpr (by positivity), ?_⟩
  intro c hc hδ
  have hR : R < max R 0 + 1 := by
    nlinarith [le_max_left R 0]
  have hinv : max R 0 + 1 < 1 / c := by
    simpa [one_div] using one_div_lt_one_div_of_lt hc hδ
  exact lt_trans hR hinv

private def chapter10Exercise105Problem
    (objective : Point → ℝ) (constraint : ι → Point → ℝ)
    (hstrictFeasible : Set.Nonempty {x : Point | ∀ i : ι, 0 < constraint i x}) :
    InteriorPointPenaltyProblem Point ι where
  objective := objective
  constraint := constraint
  strictFeasibleSet_nonempty := hstrictFeasible
  barrier := fun c ↦ 1 / c
  barrier_large_near_zero := one_div_large_near_zero
  barrier_antitone := by
    intro c₁ c₂ hc₁ h
    exact one_div_le_one_div_of_le hc₁ h.le

private theorem chapter10Exercise105Problem_hasPositiveBarrierValues
    (objective : Point → ℝ) (constraint : ι → Point → ℝ)
    (hstrictFeasible : Set.Nonempty {x : Point | ∀ i : ι, 0 < constraint i x}) :
    InteriorPointPenaltyProblem.HasPositiveBarrierValues
      (chapter10Exercise105Problem objective constraint hstrictFeasible) := by
  intro c hc
  simpa [chapter10Exercise105Problem] using one_div_pos.mpr hc

private theorem chapter10Exercise105StrictFeasibleSet_nonempty
    (objective : Point → ℝ) (constraint : ι → Point → ℝ) (x : ℝ → Point)
    (hx : ∀ {σ : ℝ}, 0 < σ →
      x σ ∈ {y : Point | ∀ i : ι, 0 < constraint i y} ∧
        IsMinOn
          (fun y ↦ objective y + (1 / σ) * ∑ i : ι, 1 / constraint i y)
          {y : Point | ∀ i : ι, 0 < constraint i y}
          (x σ)) :
    Set.Nonempty {y : Point | ∀ i : ι, 0 < constraint i y} :=
  ⟨x 1, (hx zero_lt_one).1⟩

private theorem chapter10Exercise105Problem_minimizer
    (objective : Point → ℝ) (constraint : ι → Point → ℝ) (x : ℝ → Point)
    (hstrictFeasible : Set.Nonempty {x : Point | ∀ i : ι, 0 < constraint i x})
    (hx : ∀ {σ : ℝ}, 0 < σ →
      x σ ∈ {y : Point | ∀ i : ι, 0 < constraint i y} ∧
        IsMinOn
          (fun y ↦ objective y + (1 / σ) * ∑ i : ι, 1 / constraint i y)
          {y : Point | ∀ i : ι, 0 < constraint i y}
          (x σ)) :
    ∀ {σ : ℝ}, 0 < σ →
      x σ ∈
          (chapter10Exercise105Problem objective constraint hstrictFeasible).strictFeasibleSet ∧
        IsMinOn
          ((chapter10Exercise105Problem objective constraint hstrictFeasible).penaltyFunction σ)
          (chapter10Exercise105Problem objective constraint hstrictFeasible).strictFeasibleSet
          (x σ) := by
  intro σ hσ
  refine ⟨?_, ?_⟩
  · simpa [chapter10Exercise105Problem, InteriorPointPenaltyProblem.strictFeasibleSet] using
      (hx hσ).1
  · convert (hx hσ).2 using 1
    · ext y
      simp [chapter10Exercise105Problem, InteriorPointPenaltyProblem.penaltyFunction,
        InteriorPointPenaltyProblem.barrierSum, one_div]
    · ext y
      simp [chapter10Exercise105Problem, InteriorPointPenaltyProblem.strictFeasibleSet]

section

variable (objective : Point → ℝ) (constraint : ι → Point → ℝ)
variable (x : ℝ → Point)
variable
  (hx : ∀ {σ : ℝ}, 0 < σ →
    x σ ∈ {y : Point | ∀ i : ι, 0 < constraint i y} ∧
      IsMinOn
        (fun y ↦ objective y + (1 / σ) * ∑ i : ι, 1 / constraint i y)
        {y : Point | ∀ i : ι, 0 < constraint i y}
        (x σ))

include objective constraint x hx

/-- Chapter10 Exercise 10.5 (1): if `x σ` solves the reciprocal-barrier subproblem
`min_x f(x) + (1 / σ) * ∑ i, 1 / cᵢ(x)` on the interior region
`{x | ∀ i, 0 < cᵢ(x)}` for every positive `σ`, so in particular each `x σ` lies in that
interior region,
then the achieved penalty value `P(x(σ), σ)` is non-increasing as `σ` increases. -/
theorem chapter10Exercise105_penaltyValue_nonincreasing
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) :
    objective (x σ₂) + (1 / σ₂) * ∑ i : ι, 1 / constraint i (x σ₂) ≤
      objective (x σ₁) + (1 / σ₁) * ∑ i : ι, 1 / constraint i (x σ₁) := by
  let hstrictFeasible :=
    chapter10Exercise105StrictFeasibleSet_nonempty objective constraint x hx
  simpa [chapter10Exercise105Problem,
    InteriorPointPenaltyProblem.penaltyFunction_apply] using
    InteriorPointPenaltyProblem.penaltyValue_antitone
      (chapter10Exercise105Problem objective constraint hstrictFeasible)
      x
      (chapter10Exercise105Problem_hasPositiveBarrierValues
        objective constraint hstrictFeasible)
      (chapter10Exercise105Problem_minimizer
        objective constraint x hstrictFeasible hx)
      hσ₁ hσ₁₂

/-- Chapter10 Exercise 10.5 (2): under the same reciprocal-barrier minimizer hypotheses, the
source sum `∑ i, 1 / cᵢ(x(σ))` is non-decreasing as `σ` increases. -/
theorem chapter10Exercise105_reciprocalBarrierSum_nondecreasing
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) :
    (∑ i : ι, 1 / constraint i (x σ₁)) ≤
      ∑ i : ι, 1 / constraint i (x σ₂) := by
  let hstrictFeasible :=
    chapter10Exercise105StrictFeasibleSet_nonempty objective constraint x hx
  simpa
      [chapter10Exercise105Problem,
        InteriorPointPenaltyProblem.barrierSum_apply]
    using
    InteriorPointPenaltyProblem.barrierSum_monotone
      (chapter10Exercise105Problem objective constraint hstrictFeasible)
      x
      (chapter10Exercise105Problem_minimizer
        objective constraint x hstrictFeasible hx)
      hσ₁ hσ₁₂

/-- Chapter10 Exercise 10.5 (3): under the same reciprocal-barrier minimizer hypotheses, the
objective value `f (x(σ))` is non-increasing as `σ` increases. -/
theorem chapter10Exercise105_objectiveValue_nonincreasing
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) :
    objective (x σ₂) ≤ objective (x σ₁) := by
  let hstrictFeasible :=
    chapter10Exercise105StrictFeasibleSet_nonempty objective constraint x hx
  simpa [chapter10Exercise105Problem] using
    InteriorPointPenaltyProblem.objective_antitone
      (chapter10Exercise105Problem objective constraint hstrictFeasible)
      x
      (chapter10Exercise105Problem_minimizer
        objective constraint x hstrictFeasible hx)
      hσ₁ hσ₁₂

end

#print axioms chapter10Exercise105_penaltyValue_nonincreasing
#print axioms InteriorPointPenaltyProblem.penaltyValue_antitone

end
