/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_1_extra_1

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ValuePoint" => EuclideanSpace ℝ (Fin m)
-- Domain-style sampling:
-- * primary domain: composite nonsmooth optimization problems in Euclidean spaces;
-- * inspected canonical surfaces: `Function.comp`, `OptimizationProblem`,
--   `OptimizationProblem.coeFn_apply`, `OptimizationProblem.IsUnconstrained`;
-- * source-facing owner: the composite decomposition with regularity hypotheses in this file;
-- * core/canonical owner: `OptimizationProblem` from `Chapter01.Definition_1_1_extra_1`;
-- * bridge/view: `toOptimizationProblem`, using the Euclidean coordinate equivalence.
-- Primitive data are `smoothMap`, `outerFunction`, and the Section 14.6 regularity hypotheses
-- used by the surrounding API. The objective-function and unconstrained-problem surfaces are
-- derived API and should not be stored as additional primitive data here.

/-- Chapter14 Definition 14.6-extra-1: a composite nonsmooth optimization problem on `ℝ^n`
with `m` component functions consists of a continuously differentiable inner map
`f : Point → ValuePoint` and a convex outer function `h : ValuePoint → ℝ`; its objective is the
composite function `x ↦ h (f x)`. -/
structure CompositeNonsmoothOptimizationProblem (n m : ℕ) where
  smoothMap : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)
  outerFunction : EuclideanSpace ℝ (Fin m) → ℝ
  smoothMap_contDiff : ContDiff ℝ 1 smoothMap
  outerFunction_convex : ConvexOn ℝ Set.univ outerFunction

namespace CompositeNonsmoothOptimizationProblem

/-- The source composite objective `x ↦ h (f x)` carried by the problem. -/
def objective (problem : CompositeNonsmoothOptimizationProblem n m) : Point → ℝ :=
  problem.outerFunction ∘ problem.smoothMap

/-- A composite nonsmooth optimization problem can be evaluated as its objective function. -/
instance : CoeFun (CompositeNonsmoothOptimizationProblem n m) (fun _ ↦ Point → ℝ) where
  coe problem := problem.objective

/-- Evaluating `problem.objective` at `x` gives the source composite value `h (f x)`. -/
@[simp] theorem objective_apply
    (problem : CompositeNonsmoothOptimizationProblem n m) (x : Point) :
    problem.objective x = problem.outerFunction (problem.smoothMap x) :=
  rfl

/-- Evaluating `problem` as a function at `x` expands to the composite value
`problem.outerFunction (problem.smoothMap x)`. -/
@[simp] theorem coe_apply
    (problem : CompositeNonsmoothOptimizationProblem n m) (x : Point) :
    problem x = problem.outerFunction (problem.smoothMap x) :=
  rfl

/-- Forgetting the composite presentation turns a composite nonsmooth problem into the canonical
Chapter 1 unconstrained optimization-problem owner, expressed in Euclidean coordinates. -/
def toOptimizationProblem (problem : CompositeNonsmoothOptimizationProblem n m) :
    OptimizationProblem n where
  objective := fun x ↦ problem ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
  feasibleSet := Set.univ

/-- The Chapter 1 bridge evaluates at Euclidean coordinates by the source composite formula. -/
@[simp] theorem toOptimizationProblem_apply
    (problem : CompositeNonsmoothOptimizationProblem n m) (x : Point) :
    problem.toOptimizationProblem ((EuclideanSpace.equiv (Fin n) ℝ) x) = problem x := by
  change problem ((EuclideanSpace.equiv (Fin n) ℝ).symm ((EuclideanSpace.equiv (Fin n) ℝ) x)) =
      problem x
  have hx : (EuclideanSpace.equiv (Fin n) ℝ).symm ((EuclideanSpace.equiv (Fin n) ℝ) x) = x :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm_apply_apply x
  rw [hx]

/-- The underlying Chapter 1 optimization problem is unconstrained. -/
theorem toOptimizationProblem_isUnconstrained
    (problem : CompositeNonsmoothOptimizationProblem n m) :
    problem.toOptimizationProblem.IsUnconstrained := rfl

end CompositeNonsmoothOptimizationProblem

#print axioms CompositeNonsmoothOptimizationProblem.toOptimizationProblem

end
