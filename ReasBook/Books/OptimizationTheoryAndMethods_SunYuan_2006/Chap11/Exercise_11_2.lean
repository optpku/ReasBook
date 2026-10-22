/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Tactic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Exercise_8_9

noncomputable section

section Chapter11Exercise112

local notation "Point" => EuclideanSpace ℝ (Fin 3)

-- Domain sampling:
-- * mathlib owner: `IsMinOn`
-- * project source-facing owners: `exercise89FeasibleSet`, `exercise89SquaredDistanceToOrigin`,
--   and `exercise89NearestPoint`
-- Layer triage:
-- * source-facing: the explicit ellipse and squared-distance problem already formalized in
--   Chapter 8 Exercise 8.9
-- * core/canonical: `IsMinOn` on that feasible set
-- * bridge/view: the uniqueness theorem below, with the explicit feasibility hypothesis that
--   `IsMinOn` itself does not encode

/- Chapter11 Exercise 11.2 is the same nearest-point-on-an-ellipse problem already formalized in
Chapter08 Exercise 8.9, so this file reuses the Chapter 8 source-facing owners directly instead
of reintroducing parallel local definitions. -/
#check exercise89NearestPoint_mem_feasibleSet
#check isMinOn_exercise89SquaredDistanceToOrigin

/-- Any feasible minimizer of the squared distance to the origin on the Exercise 11.2 ellipse is
the explicit point `exercise89NearestPoint = (1 / 3, 2 / 3, 0)`. The feasibility hypothesis is
essential because `IsMinOn` alone does not imply membership in `exercise89FeasibleSet`. -/
theorem chapter11Exercise112_eq_nearestPoint_of_mem_of_isMinOn
    {p : Point} (hp : p ∈ exercise89FeasibleSet)
    (hmin : IsMinOn exercise89SquaredDistanceToOrigin exercise89FeasibleSet p) :
    p = exercise89NearestPoint := by
  rcases (exercise89_mem_feasibleSet_iff p).1 hp with ⟨hxy, hquad⟩
  have hp_le :
      exercise89SquaredDistanceToOrigin p ≤
        exercise89SquaredDistanceToOrigin exercise89NearestPoint :=
    (isMinOn_iff.mp hmin) exercise89NearestPoint exercise89NearestPoint_mem_feasibleSet
  have hnearest_le :
      exercise89SquaredDistanceToOrigin exercise89NearestPoint ≤
        exercise89SquaredDistanceToOrigin p :=
    (isMinOn_iff.mp isMinOn_exercise89SquaredDistanceToOrigin) p hp
  have hobj :
      exercise89SquaredDistanceToOrigin p =
        exercise89SquaredDistanceToOrigin exercise89NearestPoint :=
    le_antisymm hp_le hnearest_le
  have hnearest_sq :
      exercise89SquaredDistanceToOrigin exercise89NearestPoint = (5 : ℝ) / 9 := by
    norm_num [exercise89SquaredDistanceToOrigin, exercise89NearestPoint_apply_zero,
      exercise89NearestPoint_apply_one, exercise89NearestPoint_apply_two]
  have hsq :
      (p 0) ^ (2 : ℕ) + (p 1) ^ (2 : ℕ) + (p 2) ^ (2 : ℕ) = (5 : ℝ) / 9 := by
    calc
      (p 0) ^ (2 : ℕ) + (p 1) ^ (2 : ℕ) + (p 2) ^ (2 : ℕ) =
          exercise89SquaredDistanceToOrigin p := by
            rfl
      _ = exercise89SquaredDistanceToOrigin exercise89NearestPoint := hobj
      _ = (5 : ℝ) / 9 := hnearest_sq
  have hy_sq : (p 1) ^ (2 : ℕ) = (4 : ℝ) / 9 := by
    nlinarith [hquad, hsq]
  have hy_nonneg : 0 ≤ p 1 := by
    nlinarith [hquad, hxy, sq_nonneg (p 2), sq_nonneg (1 - p 1)]
  have hy : p 1 = (2 : ℝ) / 3 := by
    nlinarith [hy_sq, hy_nonneg]
  have hx : p 0 = (1 : ℝ) / 3 := by
    nlinarith [hxy, hy]
  have hz_sq : (p 2) ^ (2 : ℕ) = 0 := by
    nlinarith [hquad, hx, hy]
  have hz : p 2 = 0 := by
    nlinarith [hz_sq]
  ext i
  fin_cases i
  · simpa using hx
  · simpa using hy
  · simpa using hz

end Chapter11Exercise112
