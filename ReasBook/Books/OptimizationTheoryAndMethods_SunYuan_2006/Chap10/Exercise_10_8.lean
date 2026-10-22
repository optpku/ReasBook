/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Algorithm_10_4_1

noncomputable section

open scoped BigOperators

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

namespace StandardPenaltyProblem

/-- The augmented Lagrangian of the slack-variable reformulation keeps the equality block of
`problem` unchanged and replaces each inequality constraint `cᵢ(x) ≥ 0` by the equality
`cᵢ(x) - yᵢ = 0`, where the slack variables satisfy `yᵢ ≥ 0`. -/
def slackAugmentedLagrangian
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
    (x : Point) (slack : ConstraintPoint) : ℝ :=
  problem.objective x +
    ∑ i : Fin m,
      if i.1 < problem.eqCount then
        (-(lam i) * problem.constraint i x +
          (1 / 2 : ℝ) * σ i * (problem.constraint i x) ^ (2 : ℕ))
      else
        (-(lam i) * (problem.constraint i x - slack i) +
          (1 / 2 : ℝ) * σ i * (problem.constraint i x - slack i) ^ (2 : ℕ))

/-- Evaluating `problem.slackAugmentedLagrangian lam σ x slack` expands to the source objective
and the quadratic slack-variable penalty sum. -/
@[simp] theorem slackAugmentedLagrangian_apply
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
    (x : Point) (slack : ConstraintPoint) :
    problem.slackAugmentedLagrangian lam σ x slack =
      problem.objective x +
        ∑ i : Fin m,
          if i.1 < problem.eqCount then
            (-(lam i) * problem.constraint i x +
              (1 / 2 : ℝ) * σ i * (problem.constraint i x) ^ (2 : ℕ))
          else
            (-(lam i) * (problem.constraint i x - slack i) +
              (1 / 2 : ℝ) * σ i * (problem.constraint i x - slack i) ^ (2 : ℕ)) :=
  rfl

/-- The canonical slack choice for the reformulated inequality block is
`yᵢ = max (cᵢ(x) - λᵢ / σᵢ) 0`; the equality block uses `0` because there are no slack variables
there. -/
def optimalSlack
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
    (x : Point) : ConstraintPoint :=
  WithLp.toLp 2 fun i ↦
    if i.1 < problem.eqCount then
      0
    else
      max (problem.constraint i x - lam i / σ i) 0

/-- A slack vector is admissible for the reformulated problem when its inequality-block
coordinates are nonnegative. -/
def slackNonnegative
    (problem : StandardPenaltyProblem n m) (slack : ConstraintPoint) : Prop :=
  ∀ ⦃i : Fin m⦄, problem.eqCount ≤ i.1 → 0 ≤ slack i

/-- Unfolding `problem.slackNonnegative slack` gives the source inequality-block sign
condition. -/
theorem slackNonnegative_iff
    (problem : StandardPenaltyProblem n m) (slack : ConstraintPoint) :
    problem.slackNonnegative slack ↔
      ∀ i : Fin m, problem.eqCount ≤ i.1 → 0 ≤ slack i := by
  constructor
  · intro h i hi
    exact h hi
  · intro h i hi
    exact h i hi

/-- On an equality-block coordinate, the canonical slack choice is `0`. -/
@[simp] theorem optimalSlack_apply_of_lt_eqCount
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
    (x : Point) (i : Fin m) (hi : i.1 < problem.eqCount) :
    problem.optimalSlack lam σ x i = 0 := by
  rw [StandardPenaltyProblem.optimalSlack, PiLp.toLp_apply, if_pos hi]

/-- On an inequality-block coordinate, the canonical slack choice is
`max (cᵢ(x) - λᵢ / σᵢ) 0`. -/
@[simp] theorem optimalSlack_apply_of_eqCount_le
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
    (x : Point) (i : Fin m) (hi : problem.eqCount ≤ i.1) :
    problem.optimalSlack lam σ x i =
      max (problem.constraint i x - lam i / σ i) 0 := by
  rw [StandardPenaltyProblem.optimalSlack, PiLp.toLp_apply, if_neg (not_lt_of_ge hi)]

/-- The canonical slack choice is nonnegative on the inequality block. -/
theorem optimalSlack_nonneg
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
    (x : Point) (i : Fin m) (hi : problem.eqCount ≤ i.1) :
    0 ≤ problem.optimalSlack lam σ x i := by
  rw [problem.optimalSlack_apply_of_eqCount_le lam σ x i hi]
  exact le_max_right _ _

/-- The canonical slack choice is admissible for the reformulated inequality block. -/
theorem optimalSlack_slackNonnegative
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint) (x : Point) :
    problem.slackNonnegative (problem.optimalSlack lam σ x) := by
  intro i hi
  exact problem.optimalSlack_nonneg lam σ x i hi

end StandardPenaltyProblem

/-- Helper for Chapter10 Exercise 10.8: on an inequality-block coordinate, the mixed
augmented-Lagrangian summand is bounded above by the slack-variable quadratic term for every
nonnegative slack value. -/
lemma piecewise_augmented_term_le_slack_term
    (c lam σ y : ℝ) (hσ : 0 < σ) (hy : 0 ≤ y) :
    (if c < lam / σ then
        (-(lam) * c + (1 / 2 : ℝ) * σ * c ^ (2 : ℕ))
      else
        (-((1 / 2 : ℝ) * lam ^ (2 : ℕ) / σ))) ≤
      (-(lam) * (c - y) + (1 / 2 : ℝ) * σ * (c - y) ^ (2 : ℕ)) := by
  by_cases hcase : c < lam / σ
  · -- In the active branch, moving from `c` to `c - y` only increases the quadratic term.
    have hσ0 : σ ≠ 0 := ne_of_gt hσ
    have hactive : 0 < lam - σ * c := by
      have hsub : 0 < lam / σ - c := sub_pos.mpr hcase
      have hscaled : 0 < σ * (lam / σ - c) := mul_pos hσ hsub
      have hidentity : σ * (lam / σ - c) = lam - σ * c := by
        field_simp [hσ0]
      linarith
    have hlinear : 0 ≤ y * (lam - σ * c) := mul_nonneg hy (le_of_lt hactive)
    have hquadratic : 0 ≤ (1 / 2 : ℝ) * σ * y ^ (2 : ℕ) := by
      positivity
    have hdiff :
        0 ≤
          y * (lam - σ * c) +
            (1 / 2 : ℝ) * σ * y ^ (2 : ℕ) := add_nonneg hlinear hquadratic
    have hidentity :
        (-(lam) * (c - y) + (1 / 2 : ℝ) * σ * (c - y) ^ (2 : ℕ)) -
            (-(lam) * c + (1 / 2 : ℝ) * σ * c ^ (2 : ℕ)) =
          y * (lam - σ * c) + (1 / 2 : ℝ) * σ * y ^ (2 : ℕ) := by
      ring
    rw [if_pos hcase]
    nlinarith [hdiff, hidentity]
  · -- In the inactive branch, the piecewise value is the minimum of the slack quadratic.
    let diff : ℝ :=
      (-(lam) * (c - y) + (1 / 2 : ℝ) * σ * (c - y) ^ (2 : ℕ)) -
        (-((1 / 2 : ℝ) * lam ^ (2 : ℕ) / σ))
    have hσ0 : σ ≠ 0 := ne_of_gt hσ
    have hsquare : 0 ≤ (σ * (c - y) - lam) ^ (2 : ℕ) := sq_nonneg (σ * (c - y) - lam)
    have hidentity : 2 * σ * diff = (σ * (c - y) - lam) ^ (2 : ℕ) := by
      dsimp [diff]
      field_simp [hσ0]
      ring
    have hdiff : 0 ≤ diff := by
      have hscaled : 0 ≤ 2 * σ * diff := by
        rw [hidentity]
        exact hsquare
      exact nonneg_of_mul_nonneg_right hscaled (by positivity)
    rw [if_neg hcase]
    dsimp [diff] at hdiff
    linarith

/-- Helper for Chapter10 Exercise 10.8: the canonical slack
`max (c - λ / σ) 0` reproduces the piecewise inequality-block augmented-Lagrangian term exactly. -/
lemma piecewise_augmented_term_eq_optimal_slack_term
    (c lam σ : ℝ) (hσ : 0 < σ) :
    (-(lam) * (c - max (c - lam / σ) 0) +
      (1 / 2 : ℝ) * σ * (c - max (c - lam / σ) 0) ^ (2 : ℕ)) =
      (if c < lam / σ then
          (-(lam) * c + (1 / 2 : ℝ) * σ * c ^ (2 : ℕ))
        else
          (-((1 / 2 : ℝ) * lam ^ (2 : ℕ) / σ))) := by
  by_cases hcase : c < lam / σ
  · -- When `c < λ / σ`, the optimal slack is `0`, so the mixed quadratic branch is unchanged.
    have hmax : max (c - lam / σ) 0 = 0 := by
      exact max_eq_right (le_of_lt (sub_lt_zero.mpr hcase))
    rw [hmax, if_pos hcase]
    ring
  · -- When `c ≥ λ / σ`, the optimal slack forces `c - y = λ / σ`, yielding the constant branch.
    have hσ0 : σ ≠ 0 := ne_of_gt hσ
    have hmax : max (c - lam / σ) 0 = c - lam / σ := by
      exact max_eq_left (sub_nonneg.mpr (le_of_not_gt hcase))
    rw [hmax, if_neg hcase]
    field_simp [hσ0]
    ring

/-- Helper for Chapter10 Exercise 10.8: on an inequality coordinate, evaluating the
slack-variable summand at the canonical slack reproduces the corresponding mixed summand. -/
lemma optimal_slack_inequality_summand_eq
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
    (hσ : ∀ i : Fin m, 0 < σ i) (x : Point) (i : Fin m)
    (hi : problem.eqCount ≤ i.1) :
    (-(lam i) * (problem.constraint i x - problem.optimalSlack lam σ x i) +
      (1 / 2 : ℝ) * σ i * (problem.constraint i x - problem.optimalSlack lam σ x i) ^ (2 : ℕ)) =
      (if problem.constraint i x < lam i / σ i then
          (-(lam i) * problem.constraint i x +
            (1 / 2 : ℝ) * σ i * (problem.constraint i x) ^ (2 : ℕ))
        else
          (-((1 / 2 : ℝ) * (lam i) ^ (2 : ℕ) / σ i))) := by
  -- Rewrite the canonical slack first, then apply the scalar optimal-slack identity.
  rw [problem.optimalSlack_apply_of_eqCount_le lam σ x i hi]
  simpa using
    piecewise_augmented_term_eq_optimal_slack_term
      (problem.constraint i x) (lam i) (σ i) (hσ i)

/-- For positive penalty parameters, the mixed-constraint augmented Lagrangian
`problem.augmentedLagrangian lam σ x` is pointwise bounded above by the augmented Lagrangian
of the slack-variable reformulation evaluated at any nonnegative slack vector. Thus the chapter's
mixed inequality formula is the comparison baseline for the reformulated problem. -/
theorem chapter10Exercise108_augmentedLagrangian_le_slackAugmentedLagrangian
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
    (hσ : ∀ i : Fin m, 0 < σ i) (x : Point) (slack : ConstraintPoint)
    (hslack : problem.slackNonnegative slack) :
    problem.augmentedLagrangian lam σ x ≤
      problem.slackAugmentedLagrangian lam σ x slack := by
  rw [problem.augmentedLagrangian_eq, problem.slackAugmentedLagrangian_apply]
  -- The source objective agrees on both sides, so only the coordinatewise penalty sums matter.
  let mixedSum : ℝ :=
    ∑ i : Fin m,
      if i.1 < problem.eqCount then
        (-(lam i) * problem.constraint i x +
          (1 / 2 : ℝ) * σ i * (problem.constraint i x) ^ (2 : ℕ))
      else if problem.constraint i x < lam i / σ i then
        (-(lam i) * problem.constraint i x +
          (1 / 2 : ℝ) * σ i * (problem.constraint i x) ^ (2 : ℕ))
      else
        (-((1 / 2 : ℝ) * (lam i) ^ (2 : ℕ) / σ i))
  let slackSum : ℝ :=
    ∑ i : Fin m,
      if i.1 < problem.eqCount then
        (-(lam i) * problem.constraint i x +
          (1 / 2 : ℝ) * σ i * (problem.constraint i x) ^ (2 : ℕ))
      else
        (-(lam i) * (problem.constraint i x - slack i) +
          (1 / 2 : ℝ) * σ i * (problem.constraint i x - slack i) ^ (2 : ℕ))
  have hsum : mixedSum ≤ slackSum := by
    refine Finset.sum_le_sum ?_
    intro i _
    by_cases hi : i.1 < problem.eqCount
    · -- Equality coordinates are identical in the original and slack-variable formulations.
      simp [hi]
    · -- Inequality coordinates are compared by the scalar slack-variable inequality.
      have hineq : problem.eqCount ≤ i.1 := Nat.le_of_not_gt hi
      have hslack_nonneg : 0 ≤ slack i := hslack hineq
      simpa [hi] using
        piecewise_augmented_term_le_slack_term
          (problem.constraint i x) (lam i) (σ i) (slack i) (hσ i) hslack_nonneg
  dsimp [mixedSum, slackSum] at hsum
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left hsum (problem.objective x)

/-- Chapter10 Exercise 10.8: when the slack variables are chosen as
`yᵢ = max (cᵢ(x) - λᵢ / σᵢ) 0` on the inequality block, the augmented Lagrangian of the
slack-variable reformulation agrees exactly with the chapter's mixed equality/inequality
augmented Lagrangian `problem.augmentedLagrangian lam σ x`. -/
theorem chapter10Exercise108_slackAugmentedLagrangian_eq_augmentedLagrangian
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
    (hσ : ∀ i : Fin m, 0 < σ i) (x : Point) :
    problem.slackAugmentedLagrangian lam σ x (problem.optimalSlack lam σ x) =
      problem.augmentedLagrangian lam σ x := by
  rw [problem.slackAugmentedLagrangian_apply, problem.augmentedLagrangian_eq]
  -- Compare the finite sums coordinatewise, splitting into equality and inequality blocks.
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hi : i.1 < problem.eqCount
  · -- Equality coordinates already use the same quadratic term on both sides.
    simp [hi]
  · -- Inequality coordinates match once the canonical slack is rewritten explicitly.
    have hineq : problem.eqCount ≤ i.1 := Nat.le_of_not_gt hi
    rw [if_neg hi, if_neg hi]
    exact optimal_slack_inequality_summand_eq problem lam σ hσ x i hineq

#print axioms StandardPenaltyProblem.slackAugmentedLagrangian
#print axioms StandardPenaltyProblem.optimalSlack

end
