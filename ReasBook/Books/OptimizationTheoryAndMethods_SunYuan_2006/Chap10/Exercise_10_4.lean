/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Algorithm_10_4_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Exercise_10_3

open scoped BigOperators

noncomputable section

section

local notation "Point" => EuclideanSpace ℝ (Fin 2)

-- Domain sampling:
-- * primary domain: Chapter 10 penalty-method owner surfaces for the Exercise
--   10.3/10.4 inequality-constrained problem on `ℝ²`: the augmented-Lagrangian
--   stage objective from Section 10.4 and the strict-feasible-set owner from
--   Section 10.3
-- * inspected project owner/view declarations:
--   `StandardPenaltyProblem` and `c⁽-⁾[problem]` in `Definition_10_1_extra_1`,
--   `StandardPenaltyProblem.augmentedLagrangian` and
--   `StandardPenaltyProblem.augmentedLagrangian_eq` in `Algorithm_10_4_1`,
--   `InteriorPointPenaltyProblem.toStandardPenaltyProblem` in
--   `Definition_10_3_extra_1`,
--   `InteriorPointPenaltyProblem.strictFeasibleSet` and
--   `InteriorPointPenaltyProblem.mem_strictFeasibleSet_iff` in
--   `Definition_10_3_extra_1`,
--   the inherited exercise data `chapter10Exercise103Objective`,
--   `chapter10Exercise103Constraint`, `chapter10Exercise103InitialPoint`,
--   `chapter10Exercise103BarrierMinimizer`,
--   `chapter10Exercise103_mem_strictFeasibleSet_iff`, and
--   `chapter10Exercise103Optimizer` in `Exercise_10_3`
-- * best owner abstractions: the canonical Chapter 10 owner for the constrained
--   problem surface is `chapter10Exercise103Problem.toStandardPenaltyProblem`,
--   and the stage objective is its `augmentedLagrangian`; meanwhile
--   `chapter10Exercise103Problem.strictFeasibleSet` is the canonical owner for
--   the strict-interiority statement about the barrier minimizer
-- * primitive data vs. derived API:
--   primitive data for this exercise are inherited from `chapter10Exercise103Problem`;
--   the initial augmented objective and its explicit minimizer are derived from
--   that owner together with the inherited Exercise 10.3 point data; the
--   coordinate positivity inequalities are derived from strict-feasible-set
--   membership, not primitive data

/-- The initial augmented-Lagrangian stage objective for Exercise 10.4 is the
Chapter 10 owner
`chapter10Exercise103Problem.toStandardPenaltyProblem.augmentedLagrangian`
specialized at the source initial multiplier `(1, 1)`, namely
`chapter10Exercise103InitialPoint`, and penalty vector `σ`. -/
def chapter10Exercise104InitialAugmentedObjective
    (σ : Point) (x : Point) : ℝ :=
  chapter10Exercise103Problem.toStandardPenaltyProblem.augmentedLagrangian
    chapter10Exercise103InitialPoint σ x

/-- The initial augmented-Lagrangian subproblem separates by coordinates: the
`x 0` minimizer is `0`, and the `x 1` minimizer is `2 / (σ 1 + 2)` while
`σ 1 ≤ 2`, then `1 / 2` once the penalty parameter reaches the threshold where
the constrained optimum is already selected. -/
def chapter10Exercise104InitialAugmentedMinimizer (σ : Point) : Point :=
  EuclideanSpace.single 1 (if σ 1 ≤ 2 then 2 / (σ 1 + 2) else (1 / 2 : ℝ))

/-- The explicit first augmented-Lagrangian stage minimizer for the Exercise
10.3 problem with initial multipliers `(1, 1)` is
`(0, if σ 1 ≤ 2 then 2 / (σ 1 + 2) else 1 / 2)`. -/
theorem chapter10Exercise104_initialAugmentedMinimizer_eq
    (σ : Point) :
    chapter10Exercise104InitialAugmentedMinimizer σ =
      EuclideanSpace.single 1
        (if σ 1 ≤ 2 then 2 / (σ 1 + 2) else (1 / 2 : ℝ)) :=
  rfl

/-- Helper for Chapter10 Exercise 10.4: the initial augmented-Lagrangian objective splits into
the independent `x 0` and `x 1` scalar blocks used in the source proof. -/
lemma chapter10Exercise104_initialAugmentedObjective_split
    (σ x : Point) :
    chapter10Exercise104InitialAugmentedObjective σ x =
      (if x 0 < 1 / σ 0 then
        (1 / 2 : ℝ) * σ 0 * (x 0) ^ (2 : ℕ)
      else
        x 0 - 1 / (2 * σ 0)) +
      (if x 1 < 1 / σ 1 then
        ((σ 1 + 2) / 2 : ℝ) * (x 1) ^ (2 : ℕ) - 2 * x 1
      else
        (x 1) ^ (2 : ℕ) - x 1 - 1 / (2 * σ 1)) := by
  -- Expand the owner-level augmented Lagrangian and separate the two inequality blocks.
  rw [chapter10Exercise104InitialAugmentedObjective]
  rw [chapter10Exercise103Problem.toStandardPenaltyProblem.augmentedLagrangian_eq]
  by_cases h0 : x 0 < 1 / σ 0
  · by_cases h1 : x 1 < 1 / σ 1
    · simp [InteriorPointPenaltyProblem.toStandardPenaltyProblem, chapter10Exercise103Problem,
        chapter10Exercise103Objective, chapter10Exercise103Constraint,
        chapter10Exercise103InitialPoint, Fin.sum_univ_two]
      have h0' : x 0 < (σ 0)⁻¹ := by simpa [one_div] using h0
      have h1' : x 1 < (σ 1)⁻¹ := by simpa [one_div] using h1
      rw [if_pos h0', if_pos h1', if_pos h0', if_pos h1']
      ring_nf
    · simp [InteriorPointPenaltyProblem.toStandardPenaltyProblem, chapter10Exercise103Problem,
        chapter10Exercise103Objective, chapter10Exercise103Constraint,
        chapter10Exercise103InitialPoint, Fin.sum_univ_two]
      have h0' : x 0 < (σ 0)⁻¹ := by simpa [one_div] using h0
      have h1' : ¬ x 1 < (σ 1)⁻¹ := by simpa [one_div] using h1
      rw [if_pos h0', if_neg h1', if_pos h0', if_neg h1']
      ring_nf
  · by_cases h1 : x 1 < 1 / σ 1
    · simp [InteriorPointPenaltyProblem.toStandardPenaltyProblem, chapter10Exercise103Problem,
        chapter10Exercise103Objective, chapter10Exercise103Constraint,
        chapter10Exercise103InitialPoint, Fin.sum_univ_two]
      have h0' : ¬ x 0 < (σ 0)⁻¹ := by simpa [one_div] using h0
      have h1' : x 1 < (σ 1)⁻¹ := by simpa [one_div] using h1
      rw [if_neg h0', if_pos h1', if_neg h0', if_pos h1']
      ring_nf
    · simp [InteriorPointPenaltyProblem.toStandardPenaltyProblem, chapter10Exercise103Problem,
        chapter10Exercise103Objective, chapter10Exercise103Constraint,
        chapter10Exercise103InitialPoint, Fin.sum_univ_two]
      have h0' : ¬ x 0 < (σ 0)⁻¹ := by simpa [one_div] using h0
      have h1' : ¬ x 1 < (σ 1)⁻¹ := by simpa [one_div] using h1
      rw [if_neg h0', if_neg h1', if_neg h0', if_neg h1']
      ring_nf

/-- Helper for Chapter10 Exercise 10.4: the `x 0` block is always nonnegative when `σ 0 > 0`,
so it is minimized at `x 0 = 0`. -/
lemma chapter10Exercise104_first_block_nonneg
    {σ0 t : ℝ} (hσ0 : 0 < σ0) :
    0 ≤
      if t < 1 / σ0 then
        (1 / 2 : ℝ) * σ0 * t ^ (2 : ℕ)
      else
        t - 1 / (2 * σ0) := by
  by_cases ht : t < 1 / σ0
  · -- On the active branch, the block is a positive multiple of a square.
    have hnonneg : 0 ≤ (1 / 2 : ℝ) * σ0 * t ^ (2 : ℕ) := by positivity
    rw [if_pos ht]
    exact hnonneg
  · -- On the constant branch, the threshold gives `t ≥ 1 / σ0`, leaving a positive gap.
    have hthreshold : 1 / σ0 ≤ t := le_of_not_gt ht
    have hgap : 0 ≤ t - 1 / σ0 := sub_nonneg.mpr hthreshold
    have hconst : 0 ≤ (1 : ℝ) / (2 * σ0) := by positivity
    have hsum : 0 ≤ (t - 1 / σ0) + 1 / (2 * σ0) := add_nonneg hgap hconst
    have hrearrange : t - 1 / (2 * σ0) = (t - 1 / σ0) + 1 / (2 * σ0) := by ring
    rw [if_neg ht, hrearrange]
    exact hsum

/-- Helper for Chapter10 Exercise 10.4: when `σ 1 ≤ 2`, the second scalar block is bounded below
by the source value `-2 / (σ 1 + 2)`. -/
lemma chapter10Exercise104_second_block_lower_bound_of_le_two
    {σ1 t : ℝ} (hσ1 : 0 < σ1) (hσ1_le_two : σ1 ≤ 2) :
    -(2 / (σ1 + 2 : ℝ)) ≤
      if t < 1 / σ1 then
        ((σ1 + 2) / 2 : ℝ) * t ^ (2 : ℕ) - 2 * t
      else
        t ^ (2 : ℕ) - t - 1 / (2 * σ1) := by
  by_cases ht : t < 1 / σ1
  · -- On the active branch, complete the square around the source minimizer `2 / (σ1 + 2)`.
    have hsquare :
        0 ≤ ((σ1 + 2) / 2 : ℝ) * (t - 2 / (σ1 + 2)) ^ (2 : ℕ) := by
      have hcoef : 0 ≤ ((σ1 + 2) / 2 : ℝ) := by linarith
      exact mul_nonneg hcoef (sq_nonneg _)
    have hcompleted :
        ((σ1 + 2) / 2 : ℝ) * t ^ (2 : ℕ) - 2 * t + 2 / (σ1 + 2) =
          ((σ1 + 2) / 2 : ℝ) * (t - 2 / (σ1 + 2)) ^ (2 : ℕ) := by
      field_simp [show (σ1 + 2 : ℝ) ≠ 0 by linarith]
      ring
    have hnonneg :
        0 ≤ ((σ1 + 2) / 2 : ℝ) * t ^ (2 : ℕ) - 2 * t + 2 / (σ1 + 2) := by
      rw [hcompleted]
      exact hsquare
    have hbound : -(2 / (σ1 + 2 : ℝ)) ≤ ((σ1 + 2) / 2 : ℝ) * t ^ (2 : ℕ) - 2 * t := by
      linarith
    rw [if_pos ht]
    exact hbound
  · -- On the constant branch, the block is monotone on `[1 / σ1, ∞)`, so its minimum is at the boundary.
    let u : ℝ := 1 / σ1
    have hu_threshold : u ≤ t := by
      simpa [u] using (le_of_not_gt ht)
    have hu_half : (1 / 2 : ℝ) ≤ u := by
      simpa [u] using (one_div_le_one_div_of_le hσ1 hσ1_le_two)
    have hfactor1 : 0 ≤ t - u := sub_nonneg.mpr hu_threshold
    have hfactor2 : 0 ≤ t + u - 1 := by
      nlinarith
    have hmono : 0 ≤ (t - u) * (t + u - 1) := mul_nonneg hfactor1 hfactor2
    have htail : u ^ (2 : ℕ) - u ≤ t ^ (2 : ℕ) - t := by
      have hmono_eq :
          (t - u) * (t + u - 1) = t ^ (2 : ℕ) - t - (u ^ (2 : ℕ) - u) := by
        ring
      rw [hmono_eq] at hmono
      linarith
    have hboundary :
        -(2 / (σ1 + 2 : ℝ)) ≤ (1 / σ1) ^ (2 : ℕ) - 1 / σ1 - 1 / (2 * σ1) := by
      have hsq : 0 ≤ (σ1 - 2) ^ (2 : ℕ) := sq_nonneg (σ1 - 2)
      field_simp [hσ1.ne', show (σ1 + 2 : ℝ) ≠ 0 by linarith] at hsq ⊢
      nlinarith
    have hbound :
        -(2 / (σ1 + 2 : ℝ)) ≤ t ^ (2 : ℕ) - t - 1 / (2 * σ1) := by
      have htail' : (1 / σ1) ^ (2 : ℕ) - 1 / σ1 - 1 / (2 * σ1) ≤
          t ^ (2 : ℕ) - t - 1 / (2 * σ1) := by
        simpa [u] using sub_le_sub_right htail (1 / (2 * σ1))
      exact le_trans hboundary htail'
    rw [if_neg ht]
    exact hbound

/-- Helper for Chapter10 Exercise 10.4: the source candidate `2 / (σ 1 + 2)` attains the second
block value `-2 / (σ 1 + 2)` throughout the regime `σ 1 ≤ 2`. -/
lemma chapter10Exercise104_second_block_value_at_candidate_of_le_two
    {σ1 : ℝ} (hσ1 : 0 < σ1) (hσ1_le_two : σ1 ≤ 2) :
    (if 2 / (σ1 + 2) < 1 / σ1 then
      ((σ1 + 2) / 2 : ℝ) * (2 / (σ1 + 2)) ^ (2 : ℕ) - 2 * (2 / (σ1 + 2))
    else
      (2 / (σ1 + 2)) ^ (2 : ℕ) - 2 / (σ1 + 2) - 1 / (2 * σ1)) =
      -(2 / (σ1 + 2 : ℝ)) := by
  by_cases hlt : 2 / (σ1 + 2) < 1 / σ1
  · -- In the strict case, the active quadratic branch gives the value directly.
    rw [if_pos hlt]
    field_simp [show (σ1 + 2 : ℝ) ≠ 0 by linarith]
    ring_nf
  · -- If the active-branch inequality fails while `σ1 ≤ 2`, then necessarily `σ1 = 2`.
    have hge : 1 / σ1 ≤ 2 / (σ1 + 2) := le_of_not_gt hlt
    have hσ1_eq_two : σ1 = 2 := by
      have hge' : σ1 + 2 ≤ 2 * σ1 := by
        field_simp [hσ1.ne', show (σ1 + 2 : ℝ) ≠ 0 by linarith] at hge
        simpa [mul_comm, mul_left_comm, mul_assoc] using hge
      linarith
    rw [if_neg hlt]
    norm_num [hσ1_eq_two]

/-- Helper for Chapter10 Exercise 10.4: when `2 ≤ σ 1`, the second scalar block is bounded below
by the source value `-1 / 4 - 1 / (2 * σ 1)`. -/
lemma chapter10Exercise104_second_block_lower_bound_of_two_le
    {σ1 t : ℝ} (hσ1 : 0 < σ1) (htwo_le_σ1 : 2 ≤ σ1) :
    (-1 / 4 : ℝ) - 1 / (2 * σ1) ≤
      if t < 1 / σ1 then
        ((σ1 + 2) / 2 : ℝ) * t ^ (2 : ℕ) - 2 * t
      else
        t ^ (2 : ℕ) - t - 1 / (2 * σ1) := by
  by_cases ht : t < 1 / σ1
  · -- On the active branch, first compare with `-2 / (σ1 + 2)`, then compare the two source values.
    have hsquare :
        0 ≤ ((σ1 + 2) / 2 : ℝ) * (t - 2 / (σ1 + 2)) ^ (2 : ℕ) := by
      have hcoef : 0 ≤ ((σ1 + 2) / 2 : ℝ) := by linarith
      exact mul_nonneg hcoef (sq_nonneg _)
    have hcompleted :
        ((σ1 + 2) / 2 : ℝ) * t ^ (2 : ℕ) - 2 * t + 2 / (σ1 + 2) =
          ((σ1 + 2) / 2 : ℝ) * (t - 2 / (σ1 + 2)) ^ (2 : ℕ) := by
      field_simp [show (σ1 + 2 : ℝ) ≠ 0 by linarith]
      ring
    have hnonneg :
        0 ≤ ((σ1 + 2) / 2 : ℝ) * t ^ (2 : ℕ) - 2 * t + 2 / (σ1 + 2) := by
      rw [hcompleted]
      exact hsquare
    have hactive : -(2 / (σ1 + 2 : ℝ)) ≤ ((σ1 + 2) / 2 : ℝ) * t ^ (2 : ℕ) - 2 * t := by
      linarith
    have hcompare : (-1 / 4 : ℝ) - 1 / (2 * σ1) ≤ -(2 / (σ1 + 2 : ℝ)) := by
      have hsq : 0 ≤ (σ1 - 2) ^ (2 : ℕ) := sq_nonneg (σ1 - 2)
      field_simp [hσ1.ne', show (σ1 + 2 : ℝ) ≠ 0 by linarith] at hsq ⊢
      nlinarith
    rw [if_pos ht]
    exact le_trans hcompare hactive
  · -- On the constant branch, complete the square around `1 / 2`.
    have hsquare : 0 ≤ (t - 1 / 2) ^ (2 : ℕ) := sq_nonneg _
    have hcompleted : t ^ (2 : ℕ) - t + 1 / 4 = (t - 1 / 2) ^ (2 : ℕ) := by
      ring
    have hbound : (-1 / 4 : ℝ) - 1 / (2 * σ1) ≤ t ^ (2 : ℕ) - t - 1 / (2 * σ1) := by
      rw [← hcompleted] at hsquare
      linarith
    rw [if_neg ht]
    exact hbound

/-- Chapter10 Exercise 10.4 (1): with the explicit candidate
`chapter10Exercise104InitialAugmentedMinimizer σ`, the initial
augmented-Lagrangian subproblem is minimized on `Set.univ`. -/
theorem chapter10Exercise104_initialAugmentedObjective_isMinOn
    (σ : Point) (hσ : ∀ i : Fin 2, 0 < σ i) :
    IsMinOn
      (chapter10Exercise104InitialAugmentedObjective σ)
      Set.univ
      (chapter10Exercise104InitialAugmentedMinimizer σ) := by
  refine isMinOn_iff.mpr ?_
  intro x hx
  by_cases hσ₁ : σ 1 ≤ 2
  · -- In the first regime, the source minimizer uses the active-branch critical point `2 / (σ 1 + 2)`.
    let m : Point := chapter10Exercise104InitialAugmentedMinimizer σ
    have hfirst_x :
        0 ≤
          if x 0 < 1 / σ 0 then
            (1 / 2 : ℝ) * σ 0 * (x 0) ^ (2 : ℕ)
          else
            x 0 - 1 / (2 * σ 0) :=
      chapter10Exercise104_first_block_nonneg (hσ 0)
    have hsecond_x :
        -(2 / (σ 1 + 2 : ℝ)) ≤
          if x 1 < 1 / σ 1 then
            ((σ 1 + 2) / 2 : ℝ) * (x 1) ^ (2 : ℕ) - 2 * x 1
          else
            (x 1) ^ (2 : ℕ) - x 1 - 1 / (2 * σ 1) :=
      chapter10Exercise104_second_block_lower_bound_of_le_two (hσ 1) hσ₁
    have hm_eq :
        chapter10Exercise104InitialAugmentedObjective σ m = -(2 / (σ 1 + 2 : ℝ)) := by
      -- Evaluate the minimizer exactly: the first block is `0`, and the second is the source value.
      rw [chapter10Exercise104_initialAugmentedObjective_split]
      have hm0 : m 0 = 0 := by
        simp [m, chapter10Exercise104InitialAugmentedMinimizer]
      have hm1 : m 1 = 2 / (σ 1 + 2) := by
        simp [m, chapter10Exercise104InitialAugmentedMinimizer, hσ₁]
      have hσ0_inv : 0 < 1 / σ 0 := one_div_pos.mpr (hσ 0)
      have hfirst_m :
          (if m 0 < 1 / σ 0 then
            (1 / 2 : ℝ) * σ 0 * (m 0) ^ (2 : ℕ)
          else
            m 0 - 1 / (2 * σ 0)) = 0 := by
        rw [hm0, if_pos hσ0_inv]
        ring
      have hsecond_m :
          (if m 1 < 1 / σ 1 then
            ((σ 1 + 2) / 2 : ℝ) * (m 1) ^ (2 : ℕ) - 2 * m 1
          else
            (m 1) ^ (2 : ℕ) - m 1 - 1 / (2 * σ 1)) =
            -(2 / (σ 1 + 2 : ℝ)) := by
        rw [hm1]
        simpa using
          chapter10Exercise104_second_block_value_at_candidate_of_le_two (hσ 1) hσ₁
      rw [hfirst_m, hsecond_m]
      ring
    have hlower_x :
        -(2 / (σ 1 + 2 : ℝ)) ≤ chapter10Exercise104InitialAugmentedObjective σ x := by
      -- Reassemble the two scalar lower bounds for the arbitrary comparison point `x`.
      rw [chapter10Exercise104_initialAugmentedObjective_split]
      linarith
    calc
      chapter10Exercise104InitialAugmentedObjective σ
          (chapter10Exercise104InitialAugmentedMinimizer σ)
        = -(2 / (σ 1 + 2 : ℝ)) := by simpa [m] using hm_eq
      _ ≤ chapter10Exercise104InitialAugmentedObjective σ x := hlower_x
  · -- After the threshold `σ 1 ≥ 2`, the source minimizer has already reached the constrained optimizer coordinate `1 / 2`.
    let m : Point := chapter10Exercise104InitialAugmentedMinimizer σ
    have htwo_le_σ₁ : 2 ≤ σ 1 := by linarith
    have hfirst_x :
        0 ≤
          if x 0 < 1 / σ 0 then
            (1 / 2 : ℝ) * σ 0 * (x 0) ^ (2 : ℕ)
          else
            x 0 - 1 / (2 * σ 0) :=
      chapter10Exercise104_first_block_nonneg (hσ 0)
    have hsecond_x :
        (-1 / 4 : ℝ) - 1 / (2 * σ 1) ≤
          if x 1 < 1 / σ 1 then
            ((σ 1 + 2) / 2 : ℝ) * (x 1) ^ (2 : ℕ) - 2 * x 1
          else
            (x 1) ^ (2 : ℕ) - x 1 - 1 / (2 * σ 1) :=
      chapter10Exercise104_second_block_lower_bound_of_two_le (hσ 1) htwo_le_σ₁
    have hm_eq :
        chapter10Exercise104InitialAugmentedObjective σ m =
          (-1 / 4 : ℝ) - 1 / (2 * σ 1) := by
      -- At `t = 1 / 2`, the second block is already on the constant branch.
      rw [chapter10Exercise104_initialAugmentedObjective_split]
      have hm0 : m 0 = 0 := by
        simp [m, chapter10Exercise104InitialAugmentedMinimizer]
      have hm1 : m 1 = (1 / 2 : ℝ) := by
        simp [m, chapter10Exercise104InitialAugmentedMinimizer, hσ₁]
      have hσ0_inv : 0 < 1 / σ 0 := one_div_pos.mpr (hσ 0)
      have hhalf_not_lt : ¬ (1 / 2 : ℝ) < 1 / σ 1 := by
        have hhalf_le : (1 / σ 1 : ℝ) ≤ 1 / 2 := by
          simpa using (one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) htwo_le_σ₁)
        exact not_lt_of_ge hhalf_le
      have hfirst_m :
          (if m 0 < 1 / σ 0 then
            (1 / 2 : ℝ) * σ 0 * (m 0) ^ (2 : ℕ)
          else
            m 0 - 1 / (2 * σ 0)) = 0 := by
        rw [hm0, if_pos hσ0_inv]
        ring
      have hsecond_m :
          (if m 1 < 1 / σ 1 then
            ((σ 1 + 2) / 2 : ℝ) * (m 1) ^ (2 : ℕ) - 2 * m 1
          else
            (m 1) ^ (2 : ℕ) - m 1 - 1 / (2 * σ 1)) =
            (-1 / 4 : ℝ) - 1 / (2 * σ 1) := by
        rw [hm1, if_neg hhalf_not_lt]
        ring
      rw [hfirst_m, hsecond_m]
      ring
    have hlower_x :
        (-1 / 4 : ℝ) - 1 / (2 * σ 1) ≤ chapter10Exercise104InitialAugmentedObjective σ x := by
      -- Reassemble the two scalar lower bounds for the arbitrary comparison point `x`.
      rw [chapter10Exercise104_initialAugmentedObjective_split]
      linarith
    calc
      chapter10Exercise104InitialAugmentedObjective σ
          (chapter10Exercise104InitialAugmentedMinimizer σ)
        = (-1 / 4 : ℝ) - 1 / (2 * σ 1) := by simpa [m] using hm_eq
      _ ≤ chapter10Exercise104InitialAugmentedObjective σ x := hlower_x

/-- If the second penalty coordinate already satisfies `2 ≤ σ 1`, then the
first augmented-Lagrangian stage reaches the constrained optimizer
`(0, 1 / 2)ᵀ` from Exercise 10.3. -/
theorem chapter10Exercise104_initialAugmentedMinimizer_eq_optimizer_of_two_le
    (σ : Point) (hσ₁ : 2 ≤ σ 1) :
    chapter10Exercise104InitialAugmentedMinimizer σ = chapter10Exercise103Optimizer := by
  -- Once `σ 1` passes the source threshold, the explicit minimizer is exactly `(0, 1 / 2)`.
  ext i
  fin_cases i
  · simp [chapter10Exercise104InitialAugmentedMinimizer, chapter10Exercise103Optimizer]
  · by_cases hle : σ 1 ≤ 2
    · have hEq : σ 1 = 2 := by linarith
      norm_num [chapter10Exercise104InitialAugmentedMinimizer, chapter10Exercise103Optimizer, hEq]
    · simp [chapter10Exercise104InitialAugmentedMinimizer, chapter10Exercise103Optimizer, hle]

/-- For every positive barrier parameter `τ`, the logarithmic barrier minimizer
from Exercise 10.3 lies in the canonical strict feasible set, so it remains
strictly interior instead of landing exactly on `(0, 1 / 2)ᵀ` at a finite
stage. -/
theorem chapter10Exercise104_barrierMinimizer_mem_strictFeasibleSet
    (τ : ℝ) (hτ : 0 < τ) :
    chapter10Exercise103BarrierMinimizer τ ∈
      chapter10Exercise103Problem.strictFeasibleSet := by
  -- Reuse the owner-level strict-feasibility theorem from Exercise 10.3 verbatim.
  exact chapter10Exercise103_barrierMinimizer_mem_strictFeasibleSet hτ

/-- The owner-level strict-feasibility statement for the Exercise 10.3 barrier
minimizer immediately yields the coordinatewise positivity inequalities. -/
theorem chapter10Exercise104_barrierMinimizer_positive
    (τ : ℝ) (hτ : 0 < τ) :
    0 < chapter10Exercise103BarrierMinimizer τ 0 ∧
      0 < chapter10Exercise103BarrierMinimizer τ 1 := by
  simpa [chapter10Exercise103_mem_strictFeasibleSet_iff] using
    chapter10Exercise104_barrierMinimizer_mem_strictFeasibleSet τ hτ

/-- Unfolding `chapter10Exercise104InitialAugmentedObjective σ x` gives the
specialized Chapter 10 augmented Lagrangian for the Exercise 10.3 problem,
namely the concrete source objective plus the two inequality-block summands
with initial multipliers equal to `1`. -/
theorem chapter10Exercise104InitialAugmentedObjective_eq
    (σ : Point) (x : Point) :
    chapter10Exercise104InitialAugmentedObjective σ x =
      chapter10Exercise103Objective x +
        ∑ i : Fin 2,
          if chapter10Exercise103Constraint i x <
              chapter10Exercise103InitialPoint i / σ i then
            (-(chapter10Exercise103InitialPoint i) * chapter10Exercise103Constraint i x +
              (1 / 2 : ℝ) * σ i * (chapter10Exercise103Constraint i x) ^ (2 : ℕ))
          else
            (-((1 / 2 : ℝ) * (chapter10Exercise103InitialPoint i) ^ (2 : ℕ) / σ i)) := by
  simpa [chapter10Exercise104InitialAugmentedObjective,
    InteriorPointPenaltyProblem.toStandardPenaltyProblem, chapter10Exercise103Problem,
    chapter10Exercise103Objective, chapter10Exercise103Constraint] using
    chapter10Exercise103Problem.toStandardPenaltyProblem.augmentedLagrangian_eq
      chapter10Exercise103InitialPoint σ x

#print axioms StandardPenaltyProblem.augmentedLagrangian
#print axioms chapter10Exercise104InitialAugmentedObjective
#print axioms chapter10Exercise104InitialAugmentedMinimizer

end
