/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic

noncomputable section

section Chapter08Exercise89

local notation "Point" => EuclideanSpace ℝ (Fin 3)

-- Semantic recall: `IsMinOn` is the canonical minimizer predicate for a concrete feasible set.
-- This exercise keeps the explicit feasible set, squared-distance objective, and nearest point on
-- the repo-standard carrier `Point = EuclideanSpace ℝ (Fin 3)`.

/-- The ellipse of Exercise 8.9 consists of the points `x` satisfying
`x 0 + x 1 = 1` and `x 0^2 + 2 * x 1^2 + x 2^2 = 1`. -/
def exercise89FeasibleSet : Set Point :=
  {x | x 0 + x 1 = 1 ∧ (x 0) ^ (2 : ℕ) + 2 * (x 1) ^ (2 : ℕ) + (x 2) ^ (2 : ℕ) = 1}

/-- Membership in `exercise89FeasibleSet` is exactly the pair of defining equations from
Exercise 8.9. -/
theorem exercise89_mem_feasibleSet_iff (x : Point) :
    x ∈ exercise89FeasibleSet ↔
      x 0 + x 1 = 1 ∧
        (x 0) ^ (2 : ℕ) + 2 * (x 1) ^ (2 : ℕ) + (x 2) ^ (2 : ℕ) = 1 :=
  Iff.rfl

/-- The squared distance from `x` to the origin. -/
def exercise89SquaredDistanceToOrigin (x : Point) : ℝ :=
  (x 0) ^ (2 : ℕ) + (x 1) ^ (2 : ℕ) + (x 2) ^ (2 : ℕ)

/-- The candidate nearest point from Exercise 8.9 is `(1 / 3, 2 / 3, 0)`. -/
def exercise89NearestPoint : Point :=
  EuclideanSpace.single 0 ((1 : ℝ) / 3) + EuclideanSpace.single 1 ((2 : ℝ) / 3)

@[simp] theorem exercise89NearestPoint_apply_zero :
    exercise89NearestPoint 0 = (1 : ℝ) / 3 := by
  simp [exercise89NearestPoint]

@[simp] theorem exercise89NearestPoint_apply_one :
    exercise89NearestPoint 1 = (2 : ℝ) / 3 := by
  simp [exercise89NearestPoint]

@[simp] theorem exercise89NearestPoint_apply_two :
    exercise89NearestPoint 2 = 0 := by
  simp [exercise89NearestPoint]

#print axioms exercise89FeasibleSet
#print axioms exercise89SquaredDistanceToOrigin
#print axioms exercise89NearestPoint

/-- The point `exercise89NearestPoint` lies on the ellipse of Exercise 8.9. -/
theorem exercise89NearestPoint_mem_feasibleSet :
    exercise89NearestPoint ∈ exercise89FeasibleSet := by
  -- Check the two defining equations at the explicit KKT candidate `(1 / 3, 2 / 3, 0)`.
  rw [exercise89_mem_feasibleSet_iff]
  constructor
  · norm_num [exercise89NearestPoint_apply_zero, exercise89NearestPoint_apply_one]
  · norm_num [exercise89NearestPoint_apply_zero, exercise89NearestPoint_apply_one,
      exercise89NearestPoint_apply_two, pow_two]

/-- Helper for Chapter08 Exercise 8.9: every feasible point satisfies the recentered ellipse
identity around the candidate first coordinate `1 / 3`. -/
lemma exercise89_shifted_constraint_identity (x : Point) (hx : x ∈ exercise89FeasibleSet) :
    3 * (x 0 - (1 : ℝ) / 3) ^ (2 : ℕ) + (x 2) ^ (2 : ℕ) = 2 * (x 0 - (1 : ℝ) / 3) := by
  rcases (exercise89_mem_feasibleSet_iff x).mp hx with ⟨hxy, hquad⟩
  have hy : x 1 = 1 - x 0 := by
    linarith
  have hquad' : (x 0) ^ (2 : ℕ) + 2 * (1 - x 0) ^ (2 : ℕ) + (x 2) ^ (2 : ℕ) = 1 := by
    -- Replace `x 1` using the affine constraint so the quadratic equation only involves `x 0`
    -- and `x 2`.
    simpa [hy] using hquad
  -- Recenter the remaining quadratic identity at `x 0 = 1 / 3`.
  nlinarith [hquad']

/-- Helper for Chapter08 Exercise 8.9: on the feasible ellipse, the squared distance to the origin
is the candidate value plus a nonnegative quadratic gap. -/
lemma exercise89_squaredDistance_eq_nearestPoint_add (x : Point) (hx : x ∈ exercise89FeasibleSet) :
    exercise89SquaredDistanceToOrigin x =
      exercise89SquaredDistanceToOrigin exercise89NearestPoint +
        (x 0 - (1 : ℝ) / 3) ^ (2 : ℕ) + ((2 : ℝ) / 3) * (x 2) ^ (2 : ℕ) := by
  rcases (exercise89_mem_feasibleSet_iff x).mp hx with ⟨hxy, _hquad⟩
  have hy : x 1 = 1 - x 0 := by
    linarith
  have hshift := exercise89_shifted_constraint_identity x hx
  have hnearest :
      exercise89SquaredDistanceToOrigin exercise89NearestPoint = (5 : ℝ) / 9 := by
    -- Evaluate the objective at the explicit candidate once, then reuse that scalar value.
    norm_num [exercise89SquaredDistanceToOrigin, exercise89NearestPoint_apply_zero,
      exercise89NearestPoint_apply_one, exercise89NearestPoint_apply_two, pow_two]
  calc
    exercise89SquaredDistanceToOrigin x
        = (x 0) ^ (2 : ℕ) + (1 - x 0) ^ (2 : ℕ) + (x 2) ^ (2 : ℕ) := by
            -- Eliminate `x 1` using the affine constraint before comparing to the candidate.
            simp [exercise89SquaredDistanceToOrigin, hy]
    _ = (5 : ℝ) / 9 + (x 0 - (1 : ℝ) / 3) ^ (2 : ℕ) + ((2 : ℝ) / 3) * (x 2) ^ (2 : ℕ) := by
          -- The shifted feasible-set identity turns the objective into the candidate value plus a
          -- quadratic correction.
          nlinarith [hshift]
    _ = exercise89SquaredDistanceToOrigin exercise89NearestPoint +
          (x 0 - (1 : ℝ) / 3) ^ (2 : ℕ) + ((2 : ℝ) / 3) * (x 2) ^ (2 : ℕ) := by
          rw [← hnearest]

/-- Chapter08 Exercise 8.9: the point `exercise89NearestPoint = (1 / 3, 2 / 3, 0)` minimizes the
squared distance to the origin on the ellipse defined by `x 0 + x 1 = 1` and
`x 0^2 + 2 * x 1^2 + x 2^2 = 1`. -/
theorem isMinOn_exercise89SquaredDistanceToOrigin :
    IsMinOn exercise89SquaredDistanceToOrigin exercise89FeasibleSet exercise89NearestPoint :=
  by
  refine isMinOn_iff.mpr ?_
  intro x hx
  have hgap := exercise89_squaredDistance_eq_nearestPoint_add x hx
  -- Rewrite the target value as the candidate value plus a manifestly nonnegative correction.
  rw [hgap]
  have hsq0 : 0 ≤ (x 0 - (1 : ℝ) / 3) ^ (2 : ℕ) := by
    exact sq_nonneg (x 0 - (1 : ℝ) / 3)
  have hsq2 : 0 ≤ (x 2) ^ (2 : ℕ) := by
    exact sq_nonneg (x 2)
  have hscaled : 0 ≤ ((2 : ℝ) / 3) * (x 2) ^ (2 : ℕ) := by
    exact mul_nonneg (by norm_num) hsq2
  -- Nonnegativity of the two correction terms gives the minimizer inequality immediately.
  linarith

end Chapter08Exercise89
