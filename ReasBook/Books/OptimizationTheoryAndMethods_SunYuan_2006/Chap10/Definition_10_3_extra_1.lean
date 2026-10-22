/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_1_extra_1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Extr

noncomputable section

section Chapter10Definition103Extra1

open scoped BigOperators

-- Domain sampling:
-- * `StandardPenaltyProblem` in `Definition_10_1_extra_1` is the chapter's canonical owner for
--   objective/constraint/feasible-set data.
-- * `PenaltyFunction` in the same file keeps penalty-specific data separate from that owner.
-- * `InteriorPointPenaltyFunctionMethod` in `Algorithm_10_3_3` uses the same strict-feasibility
--   and barrier-penalty surfaces downstream.
-- This file therefore keeps only the barrier-specific source data in the owner, exposes the
-- intrinsic strict-feasible and penalty-function API generically over a decision type and finite
-- constraint index type, and adds a thin bridge back to the chapter's concrete
-- `StandardPenaltyProblem` surface when the ambient space is `EuclideanSpace ℝ (Fin n)`.

variable {Point : Type*} {ι : Type*} [Fintype ι]

/-- Chapter10 Definition 10.3-extra-1: an interior point penalty problem on a decision space
`Point` with finitely many inequality constraints indexed by `ι` consists of an objective `f`,
constraint functions `cᵢ`, a nonempty strict feasible region `{x | ∀ i, 0 < cᵢ(x)}`, and a
barrier term `h` whose values become arbitrarily large as `c → 0+` and which decreases as the
constraint value increases. The associated penalty objective is
`Pσ(x) = f x + (1 / σ) * ∑ i, h (cᵢ x)`, to be minimized on the strict feasible region. -/
structure InteriorPointPenaltyProblem (Point : Type*) (ι : Type*) [Fintype ι] where
  objective : Point → ℝ
  constraint : ι → Point → ℝ
  strictFeasibleSet_nonempty : Set.Nonempty {x : Point | ∀ i : ι, 0 < constraint i x}
  barrier : ℝ → ℝ
  barrier_large_near_zero :
    ∀ R : ℝ, ∃ δ > 0, ∀ ⦃c : ℝ⦄, 0 < c → c < δ → R < barrier c
  barrier_antitone :
    ∀ ⦃c₁ c₂ : ℝ⦄, 0 < c₁ → c₁ < c₂ → barrier c₂ ≤ barrier c₁

namespace InteriorPointPenaltyProblem

/-- The feasible set of `problem` is cut out by the inequalities `cᵢ(x) ≥ 0`. -/
def feasibleSet (problem : InteriorPointPenaltyProblem Point ι) : Set Point :=
  {x | ∀ i : ι, 0 ≤ problem.constraint i x}

/-- Feasibility in `problem` is membership in `problem.feasibleSet`. -/
instance : Membership Point (InteriorPointPenaltyProblem Point ι) where
  mem problem x := x ∈ problem.feasibleSet

/-- The strict feasible set of `problem` is the source interior region `int(X)`. -/
def strictFeasibleSet (problem : InteriorPointPenaltyProblem Point ι) : Set Point :=
  {x | ∀ i : ι, 0 < problem.constraint i x}

/-- Membership in `problem.feasibleSet` is exactly the conjunction of the weak inequalities
`cᵢ(x) ≥ 0`. -/
theorem mem_feasibleSet_iff
    (problem : InteriorPointPenaltyProblem Point ι) (x : Point) :
    x ∈ problem.feasibleSet ↔ ∀ i : ι, 0 ≤ problem.constraint i x :=
  Iff.rfl

/-- Membership in `problem.strictFeasibleSet` is exactly the conjunction of the strict
inequalities `cᵢ(x) > 0`. -/
theorem mem_strictFeasibleSet_iff
    (problem : InteriorPointPenaltyProblem Point ι) (x : Point) :
    x ∈ problem.strictFeasibleSet ↔ ∀ i : ι, 0 < problem.constraint i x :=
  Iff.rfl

/-- Every strictly feasible point is feasible. -/
theorem strictFeasibleSet_subset_feasibleSet
    (problem : InteriorPointPenaltyProblem Point ι) :
    problem.strictFeasibleSet ⊆ problem.feasibleSet := by
  intro x hx i
  exact le_of_lt (hx i)

/-- The source barrier sum at `x` is `∑ i, h (cᵢ(x))`. -/
def barrierSum (problem : InteriorPointPenaltyProblem Point ι) (x : Point) : ℝ := by
  classical
  exact ∑ i : ι, problem.barrier (problem.constraint i x)

/-- Evaluating `problem.barrierSum x` expands to the source sum `∑ i, h (cᵢ(x))`. -/
theorem barrierSum_apply
    (problem : InteriorPointPenaltyProblem Point ι) (x : Point) :
    problem.barrierSum x = ∑ i : ι, problem.barrier (problem.constraint i x) := by
  classical
  simp [barrierSum]

/-- The barrier objective `Pσ` attached to `problem` as the raw algebraic expression
`f x + (1 / σ) * ∑ i, h (cᵢ x)`. The source subproblem and minimizer API below additionally
record the barrier-parameter assumption `0 < σ`. -/
def penaltyFunction (problem : InteriorPointPenaltyProblem Point ι) (σ : ℝ) (x : Point) : ℝ :=
  problem.objective x + (1 / σ) * problem.barrierSum x

/-- Evaluating `problem.penaltyFunction σ` expands to the source formula
`f x + (1 / σ) * ∑ i, h (cᵢ x)`. -/
theorem penaltyFunction_apply
    (problem : InteriorPointPenaltyProblem Point ι) (σ : ℝ) (x : Point) :
    problem.penaltyFunction σ x =
      problem.objective x + (1 / σ) * ∑ i : ι, problem.barrier (problem.constraint i x) := by
  classical
  simp [penaltyFunction, barrierSum]

/-- `problem.HasPositiveBarrierValues` records the optional source condition `h(c) > 0` for all
`c > 0`. -/
def HasPositiveBarrierValues (problem : InteriorPointPenaltyProblem Point ι) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → 0 < problem.barrier c

/-- Unfolding `problem.HasPositiveBarrierValues` gives positivity of the barrier term on the
positive half-line. -/
theorem hasPositiveBarrierValues_iff
    (problem : InteriorPointPenaltyProblem Point ι) :
    problem.HasPositiveBarrierValues ↔ ∀ ⦃c : ℝ⦄, 0 < c → 0 < problem.barrier c :=
  Iff.rfl

/- For a positive barrier parameter `σ`, the source subproblem is stated directly on the
canonical mathlib minimizer surface
`IsMinOn (problem.penaltyFunction σ) problem.strictFeasibleSet xσ`. -/

section StandardPenaltyBridge

variable {n m : ℕ}

local notation "EuclideanPoint" => EuclideanSpace ℝ (Fin n)

/-- Forgetting the barrier data turns an interior-point penalty problem on `ℝ^n` with `m`
inequality constraints into the chapter's standard constrained problem with no equality
constraints. -/
def toStandardPenaltyProblem
    (problem : InteriorPointPenaltyProblem EuclideanPoint (Fin m)) :
    StandardPenaltyProblem n m where
  eqCount := 0
  eqCount_le := Nat.zero_le m
  objective := problem.objective
  constraint := problem.constraint

/-- The chapter's feasible-set surface for `problem.toStandardPenaltyProblem` agrees with the
weak-inequality feasible set already attached to `problem`. -/
theorem toStandardPenaltyProblem_feasibleSet
    (problem : InteriorPointPenaltyProblem EuclideanPoint (Fin m)) :
    problem.toStandardPenaltyProblem.feasibleSet = problem.feasibleSet := by
  ext x
  simp [toStandardPenaltyProblem, StandardPenaltyProblem.feasibleSet, feasibleSet]

/-- Feasibility in `problem.toStandardPenaltyProblem` is exactly weak feasibility for `problem`. -/
theorem mem_toStandardPenaltyProblem_iff
    (problem : InteriorPointPenaltyProblem EuclideanPoint (Fin m)) (x : EuclideanPoint) :
    x ∈ problem.toStandardPenaltyProblem ↔ x ∈ problem := by
  change x ∈ problem.toStandardPenaltyProblem.feasibleSet ↔ x ∈ problem.feasibleSet
  simp [toStandardPenaltyProblem_feasibleSet]

end StandardPenaltyBridge

end InteriorPointPenaltyProblem

#print axioms InteriorPointPenaltyProblem.feasibleSet
#print axioms InteriorPointPenaltyProblem.penaltyFunction

end Chapter10Definition103Extra1
