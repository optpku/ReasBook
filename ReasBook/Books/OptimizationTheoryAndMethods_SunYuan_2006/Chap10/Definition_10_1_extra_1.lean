/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Filter

noncomputable section

section Chapter10Definition101Extra1

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

-- Domain sampling:
-- * primary domain: Chapter 10 penalty methods for mixed equality/inequality constrained
--   optimization problems on `ℝ^n`
-- * inspected project owner/view declarations:
--   `QuadraticProgram.lagrangian` together with the notation surface `ℒ[P]` and `Λ[P]` in
--   Chapter 9 as the chapter's owner-notation precedent,
--   `StandardPenaltyProblem.constraintViolation` and `PenaltyFunction` in this file as the
--   source-facing problem owner and the penalty-layer owner,
--   `PenaltyFunction.nonsmoothExact` in `Definition_10_6_extra_1` as direct downstream reuse of
--   the same violation owner
-- * best owner abstraction for the textbook object `c⁽-⁾(x)`: the problem-owned map
--   `StandardPenaltyProblem.constraintViolation`; notation should therefore be a thin bridge, not
--   a second owner
-- * primitive data vs. derived API:
--   primitive problem data are `eqCount`, `objective`, and `constraint`;
--   `feasibleSet`, `constraintMap`, `constraintViolation`, and penalty evaluation are derived from
--   that owner data

/-- The feasible constraint-value set for an equality/inequality split with the first
`eqCount` coordinates constrained to vanish and the remaining coordinates constrained to be
nonnegative. -/
def feasibleConstraintValueSet (eqCount : ℕ) : Set ConstraintPoint :=
  {c | (∀ i : Fin m, i.1 < eqCount → c i = 0) ∧
      ∀ i : Fin m, eqCount ≤ i.1 → 0 ≤ c i}

/-- Membership in `feasibleConstraintValueSet eqCount` is exactly the source equality/inequality
sign condition on the constraint-value vector. -/
theorem mem_feasibleConstraintValueSet_iff
    (eqCount : ℕ) (c : ConstraintPoint) :
    c ∈ feasibleConstraintValueSet eqCount ↔
      (∀ i : Fin m, i.1 < eqCount → c i = 0) ∧
        ∀ i : Fin m, eqCount ≤ i.1 → 0 ≤ c i :=
  Iff.rfl

/-- A constrained optimization problem with contiguous equality and inequality blocks: the first
`eqCount` constraints are equalities `cᵢ(x) = 0`, and the remaining constraints are inequalities
`cᵢ(x) ≥ 0`. -/
structure StandardPenaltyProblem (n m : ℕ) where
  eqCount : ℕ
  eqCount_le : eqCount ≤ m
  objective : EuclideanSpace ℝ (Fin n) → ℝ
  constraint : Fin m → EuclideanSpace ℝ (Fin n) → ℝ

namespace StandardPenaltyProblem

/-- The feasible set consists of the points satisfying each equality constraint exactly and each
inequality constraint weakly. -/
def feasibleSet (problem : StandardPenaltyProblem n m) : Set Point :=
  {x | (∀ i : Fin m, i.1 < problem.eqCount → problem.constraint i x = 0) ∧
      ∀ i : Fin m, problem.eqCount ≤ i.1 → 0 ≤ problem.constraint i x}

/-- Feasibility in `StandardPenaltyProblem` is membership in its feasible set. -/
instance : Membership Point (StandardPenaltyProblem n m) where
  mem problem x := x ∈ problem.feasibleSet

/-- The feasible constraint-value set `C` consists of the vectors whose equality coordinates are
`0` and whose inequality coordinates are nonnegative. -/
def feasibleConstraintSet (problem : StandardPenaltyProblem n m) : Set ConstraintPoint :=
  feasibleConstraintValueSet problem.eqCount

/-- The constraint-value map `x ↦ c(x)` records the values of all constraints at `x`. -/
def constraintMap (problem : StandardPenaltyProblem n m) (x : Point) : ConstraintPoint :=
  WithLp.toLp 2 fun i ↦ problem.constraint i x

/-- Evaluating `problem.constraintMap x` unfolds to the source vector `c(x)`. -/
theorem constraintMap_eq (problem : StandardPenaltyProblem n m) (x : Point) :
    problem.constraintMap x = WithLp.toLp 2 (fun i ↦ problem.constraint i x) :=
  rfl

/-- The source violation vector `c⁻(x)` keeps equality constraints unchanged and replaces each
inequality constraint value by `min (cᵢ(x)) 0`. -/
def constraintViolation (problem : StandardPenaltyProblem n m) (x : Point) : ConstraintPoint :=
  WithLp.toLp 2 fun i ↦
    if i.1 < problem.eqCount then problem.constraint i x else min (problem.constraint i x) 0

/-- The source violation vector of `problem` is written `c⁽-⁾[problem]`, so its value at `x` is
`c⁽-⁾[problem] x`. -/
notation:max "c⁽-⁾[" problem "]" => constraintViolation problem

/-- Evaluating `c⁽-⁾[problem] x` unfolds to the source vector `c⁽-⁾(x)`. -/
theorem constraintViolation_eq (problem : StandardPenaltyProblem n m) (x : Point) :
    c⁽-⁾[problem] x =
      WithLp.toLp 2
        (fun i ↦
          if i.1 < problem.eqCount then
            problem.constraint i x
          else
            min (problem.constraint i x) 0) :=
  rfl

/-- Membership in `problem.feasibleSet` is exactly the conjunction of the equality and inequality
constraints. -/
theorem mem_feasibleSet_iff (problem : StandardPenaltyProblem n m) (x : Point) :
    x ∈ problem.feasibleSet ↔
      (∀ i : Fin m, i.1 < problem.eqCount → problem.constraint i x = 0) ∧
        ∀ i : Fin m, problem.eqCount ≤ i.1 → 0 ≤ problem.constraint i x :=
  Iff.rfl

/-- Membership in `problem.feasibleConstraintSet` is exactly the source sign condition defining
the feasible constraint-value region `C`. -/
theorem mem_feasibleConstraintSet_iff
    (problem : StandardPenaltyProblem n m) (c : ConstraintPoint) :
    c ∈ problem.feasibleConstraintSet ↔
      (∀ i : Fin m, i.1 < problem.eqCount → c i = 0) ∧
        ∀ i : Fin m, problem.eqCount ≤ i.1 → 0 ≤ c i :=
  mem_feasibleConstraintValueSet_iff problem.eqCount c

/-- A point is feasible exactly when its constraint-value vector belongs to the feasible
constraint-value set `C`. -/
theorem mem_iff_constraintMap_mem_feasibleConstraintSet
    (problem : StandardPenaltyProblem n m) (x : Point) :
    x ∈ problem ↔ problem.constraintMap x ∈ problem.feasibleConstraintSet := by
  constructor
  · intro hx
    -- Feasibility on points and on constraint vectors are the same coordinatewise conditions.
    rw [problem.mem_feasibleConstraintSet_iff]
    simpa [StandardPenaltyProblem.constraintMap, PiLp.toLp_apply]
      using (problem.mem_feasibleSet_iff x).1 hx
  · intro hx
    -- The feasible constraint-value conditions transfer back to the original point.
    exact (problem.mem_feasibleSet_iff x).2 <| by
      rw [problem.mem_feasibleConstraintSet_iff] at hx
      simpa [StandardPenaltyProblem.constraintMap, PiLp.toLp_apply] using hx

/-- A point is feasible exactly when its constraint-violation vector vanishes. -/
theorem mem_iff_constraintViolation_eq_zero
    (problem : StandardPenaltyProblem n m) (x : Point) :
    x ∈ problem ↔ c⁽-⁾[problem] x = 0 := by
  constructor
  · intro hx
    -- Each feasible coordinate of `c⁽-⁾(x)` collapses to `0`.
    ext i
    rcases (problem.mem_feasibleSet_iff x).1 hx with ⟨hEq, hIneq⟩
    by_cases hi : i.1 < problem.eqCount
    · simpa [StandardPenaltyProblem.constraintViolation, PiLp.toLp_apply, hi]
        using hEq i hi
    · have hige : problem.eqCount ≤ i.1 := Nat.le_of_not_lt hi
      have hnonneg : 0 ≤ problem.constraint i x := hIneq i hige
      simp [StandardPenaltyProblem.constraintViolation, PiLp.toLp_apply, hi, min_eq_right hnonneg]
  · intro hzero
    -- Reading the zero vector coordinatewise recovers the equality and inequality conditions.
    exact (problem.mem_feasibleSet_iff x).2 <| by
      constructor
      · intro i hi
        have hcoord := congrArg (fun c : ConstraintPoint ↦ c i) hzero
        simpa [StandardPenaltyProblem.constraintViolation, PiLp.toLp_apply, hi] using hcoord
      · intro i hi
        have hcoord := congrArg (fun c : ConstraintPoint ↦ c i) hzero
        by_cases hci : problem.constraint i x ≤ 0
        · have hzeroCoord : problem.constraint i x = 0 := by
            simpa [StandardPenaltyProblem.constraintViolation, PiLp.toLp_apply, hi,
              min_eq_left hci] using hcoord
          linarith
        · linarith

/-- Helper for Chapter10 Definition 10.1-extra-1: if `y` is a feasible inequality coordinate,
then the clipped violation `min a 0` is no larger in absolute value than the distance to `y`. -/
lemma abs_min_zero_le_abs_sub_of_nonneg (a y : ℝ) (hy : 0 ≤ y) :
    |min a 0| ≤ |a - y| := by
  -- Split by the sign of `a`, so `min a 0` becomes either `a` or `0`.
  by_cases ha : a ≤ 0
  · rw [min_eq_left ha, abs_of_nonpos ha, abs_of_nonpos]
    · linarith
    · linarith
  · have ha' : 0 ≤ a := le_of_lt (lt_of_not_ge ha)
    rw [min_eq_right ha']
    simpa using (abs_nonneg (a - y))

/-- The Euclidean norm of the violation vector equals the distance from `c(x)` to the feasible
constraint-value set `C`. This is the source formula `‖c⁻(x)‖₂ = dist (c(x), C)`. -/
theorem norm_constraintViolation_eq_infDist
    (problem : StandardPenaltyProblem n m) (x : Point) :
    ‖c⁽-⁾[problem] x‖ =
      Metric.infDist (problem.constraintMap x) problem.feasibleConstraintSet := by
  let y0 : ConstraintPoint :=
    WithLp.toLp 2 fun i ↦
      if i.1 < problem.eqCount then 0 else max (problem.constraint i x) 0
  have hy0_mem : y0 ∈ problem.feasibleConstraintSet := by
    -- The clipped witness satisfies the equality block exactly and the inequality block
    -- by construction.
    rw [problem.mem_feasibleConstraintSet_iff]
    constructor
    · intro i hi
      simp [y0, PiLp.toLp_apply, hi]
    · intro i hi
      simpa [y0, PiLp.toLp_apply, not_lt_of_ge hi] using le_max_right (problem.constraint i x) 0
  have hy0_dist :
      dist (problem.constraintMap x) y0 = ‖c⁽-⁾[problem] x‖ := by
    -- Route correction: normalize the easy direction by identifying the difference vector
    -- with `c⁽-⁾(x)` coordinatewise instead of unfolding the full norm expression.
    rw [dist_eq_norm]
    have hsub : problem.constraintMap x - y0 = c⁽-⁾[problem] x := by
      ext i
      by_cases hi : i.1 < problem.eqCount
      · simp [StandardPenaltyProblem.constraintMap, StandardPenaltyProblem.constraintViolation,
          y0, PiLp.toLp_apply, hi]
      · have hige : problem.eqCount ≤ i.1 := Nat.le_of_not_lt hi
        by_cases hci : problem.constraint i x ≤ 0
        · simp [StandardPenaltyProblem.constraintMap, StandardPenaltyProblem.constraintViolation,
            y0, PiLp.toLp_apply, hi, hige, max_eq_right hci, min_eq_left hci]
        · have hci' : 0 ≤ problem.constraint i x := le_of_lt (lt_of_not_ge hci)
          simp [StandardPenaltyProblem.constraintMap, StandardPenaltyProblem.constraintViolation,
            y0, PiLp.toLp_apply, hi, hige, max_eq_left hci', min_eq_right hci']
    simpa [hsub]
  refine le_antisymm ?_ ?_
  · -- Compare squared coordinates against an arbitrary feasible constraint vector.
    refine (Metric.le_infDist ⟨y0, hy0_mem⟩).2 ?_
    intro y hy
    have hsq :
        ‖c⁽-⁾[problem] x‖ ^ (2 : ℕ) ≤ dist (problem.constraintMap x) y ^ (2 : ℕ) := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.dist_sq_eq]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      by_cases hi : i.1 < problem.eqCount
      · have hyi : y i = 0 := (problem.mem_feasibleConstraintSet_iff y).1 hy |>.1 i hi
        simp [StandardPenaltyProblem.constraintMap, StandardPenaltyProblem.constraintViolation,
          PiLp.toLp_apply, hi, hyi, Real.dist_eq]
      · have hige : problem.eqCount ≤ i.1 := Nat.le_of_not_lt hi
        have hyi : 0 ≤ y i := (problem.mem_feasibleConstraintSet_iff y).1 hy |>.2 i hige
        have hcoord :
            ‖(c⁽-⁾[problem] x) i‖ ≤ dist ((problem.constraintMap x) i) (y i) := by
          simpa [StandardPenaltyProblem.constraintMap, StandardPenaltyProblem.constraintViolation,
            PiLp.toLp_apply, hi, Real.dist_eq]
            using abs_min_zero_le_abs_sub_of_nonneg (problem.constraint i x) (y i) hyi
        exact pow_le_pow_left₀ (norm_nonneg _) hcoord 2
    have hnorm_nonneg : 0 ≤ ‖c⁽-⁾[problem] x‖ := norm_nonneg _
    have hdist_nonneg : 0 ≤ dist (problem.constraintMap x) y := dist_nonneg
    nlinarith
  · -- The clipped feasible witness realizes the reverse inequality.
    calc
      Metric.infDist (problem.constraintMap x) problem.feasibleConstraintSet
          ≤ dist (problem.constraintMap x) y0 :=
        Metric.infDist_le_dist_of_mem hy0_mem
      _ = ‖c⁽-⁾[problem] x‖ := hy0_dist

end StandardPenaltyProblem

/-- Chapter10 Definition 10.1-extra-1: a penalty function for `problem` is obtained from a penalty
term `h : ℝ^m → ℝ` with `h 0 = 0` and `h c → +∞` as `c` tends to infinity, and is evaluated by
`x ↦ f(x) + h (c⁽-⁾[problem] x)`, where `c⁽-⁾[problem] x` is the source constraint-violation
vector. -/
structure PenaltyFunction (problem : StandardPenaltyProblem n m) where
  penaltyTerm : EuclideanSpace ℝ (Fin m) → ℝ
  penaltyTerm_zero : penaltyTerm 0 = 0
  penaltyTerm_tendsto_atTop :
    Tendsto penaltyTerm (cocompact ConstraintPoint) atTop

namespace PenaltyFunction

variable {problem : StandardPenaltyProblem n m}

/-- Evaluating a penalty function adds the objective value to the penalty term applied to the
constraint-violation vector. -/
def toFun (P : PenaltyFunction problem) (x : Point) : ℝ :=
  problem.objective x + P.penaltyTerm (c⁽-⁾[problem] x)

/-- A penalty function can be evaluated as a real-valued function on the decision space. -/
instance : CoeFun (PenaltyFunction problem) (fun _ ↦ Point → ℝ) where
  coe P := P.toFun

/-- Evaluating `P` at `x` expands to the source formula `f(x) + h (c⁽-⁾[problem] x)`. -/
theorem coe_apply (P : PenaltyFunction problem) (x : Point) :
    P x = problem.objective x + P.penaltyTerm (c⁽-⁾[problem] x) :=
  rfl

/-- On feasible points, a penalty function agrees with the original objective. -/
theorem eq_objective_of_mem_feasibleSet
    (P : PenaltyFunction problem) {x : Point} (hx : x ∈ problem) :
    P x = problem.objective x := by
  -- Feasibility kills the penalty term because the violation vector is exactly zero.
  rw [P.coe_apply, (problem.mem_iff_constraintViolation_eq_zero x).1 hx, P.penaltyTerm_zero, add_zero]

/-- The quadratic penalty term `c ↦ σ * ‖c‖²` vanishes at `0`. -/
theorem quadraticPenaltyTerm_zero (σ : ℝ) :
    (fun c : ConstraintPoint ↦ σ * ‖c‖ ^ (2 : ℕ)) 0 = 0 := by
  simp

/-- For a positive penalty parameter `σ`, the quadratic penalty term tends to `+∞` along the
cocompact filter on `ℝ^m`. -/
theorem quadraticPenaltyTerm_tendsto_atTop (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun c : ConstraintPoint ↦ σ * ‖c‖ ^ (2 : ℕ))
      (cocompact ConstraintPoint) atTop := by
  -- Cocompact norm growth passes to the square and then to multiplication by a positive constant.
  have hnorm :
      Tendsto (fun c : ConstraintPoint ↦ ‖c‖) (cocompact ConstraintPoint) atTop :=
    by
      simpa [dist_eq_norm] using
        (tendsto_dist_right_cocompact_atTop (0 : ConstraintPoint))
  have hpow :
      Tendsto (fun c : ConstraintPoint ↦ ‖c‖ ^ (2 : ℕ))
        (cocompact ConstraintPoint) atTop := by
    exact (tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by decide)).comp hnorm
  exact Tendsto.const_mul_atTop hσ hpow

/-- The Courant quadratic penalty function with positive penalty parameter `σ`. -/
def quadratic (problem : StandardPenaltyProblem n m) (σ : ℝ) (hσ : 0 < σ) :
    PenaltyFunction problem where
  penaltyTerm := fun c ↦ σ * ‖c‖ ^ (2 : ℕ)
  penaltyTerm_zero := quadraticPenaltyTerm_zero σ
  penaltyTerm_tendsto_atTop := quadraticPenaltyTerm_tendsto_atTop σ hσ

/-- Evaluating the quadratic penalty function expands to
`f(x) + σ * ‖c⁽-⁾[problem] x‖²`. -/
theorem quadratic_apply
    (problem : StandardPenaltyProblem n m) (σ : ℝ) (hσ : 0 < σ) (x : Point) :
    quadratic problem σ hσ x =
      problem.objective x + σ * ‖c⁽-⁾[problem] x‖ ^ (2 : ℕ) :=
  rfl

end PenaltyFunction

#print axioms StandardPenaltyProblem.constraintViolation
#print axioms PenaltyFunction.toFun

end Chapter10Definition101Extra1
