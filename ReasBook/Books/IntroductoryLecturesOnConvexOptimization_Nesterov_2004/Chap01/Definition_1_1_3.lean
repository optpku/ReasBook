/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- A comparison sign used in a scalar constraint against `0`. -/
inductive ConstraintSense where
  | le
  | ge
  | eq

/-- Interprets a constraint sign as the corresponding relation with `0`. -/
def ConstraintSense.Holds (sense : ConstraintSense) (value : ℝ) : Prop :=
  match sense with
  | .le => value ≤ 0
  | .ge => value ≥ 0
  | .eq => value = 0

namespace ConstraintSense

/-- Strict satisfaction of a scalar constraint against `0`. -/
def StrictHolds (sense : ConstraintSense) (value : ℝ) : Prop :=
  match sense with
  | .le => value < 0
  | .ge => value > 0
  | .eq => value = 0

/-- Strict satisfaction of a constraint implies ordinary satisfaction. -/
theorem StrictHolds.holds {sense : ConstraintSense} {value : ℝ}
    (h : sense.StrictHolds value) : sense.Holds value := by
  cases sense with
  | le =>
      exact le_of_lt h
  | ge =>
      exact le_of_lt h
  | eq =>
      exact h

end ConstraintSense

/-- A minimization problem on an ambient type `X` with a basic feasible set, a real-valued
objective on that set, and finitely many scalar constraints with comparison senses. -/
structure FunctionalConstraintsMinimizationProblem (X : Type u) (m : ℕ) where
  basicFeasibleSet : Set X
  objective : basicFeasibleSet → ℝ
  constraints : Fin m → basicFeasibleSet → ℝ
  senses : Fin m → ConstraintSense

/-- The textbook `ℝⁿ` specialization of the ambient functional-constraint owner. -/
abbrev GeneralMinimizationProblem (n m : ℕ) :=
  FunctionalConstraintsMinimizationProblem (EuclideanSpace ℝ (Fin n)) m

/-- A point of the basic feasible set is feasible if it satisfies every scalar constraint. -/
def FunctionalConstraintsMinimizationProblem.IsFeasible {X : Type u} {m : ℕ}
    (problem : FunctionalConstraintsMinimizationProblem X m)
    (x : problem.basicFeasibleSet) : Prop :=
  ∀ i, (problem.senses i).Holds (problem.constraints i x)

/-- The feasible set of a minimization problem, viewed as a subset of the basic feasible set. -/
def FunctionalConstraintsMinimizationProblem.feasibleSet {X : Type u} {m : ℕ}
    (problem : FunctionalConstraintsMinimizationProblem X m) : Set problem.basicFeasibleSet :=
  {x | problem.IsFeasible x}

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type u} {m : ℕ} {problem : FunctionalConstraintsMinimizationProblem X m}

/-- Membership in the owner feasible set is exactly the owner feasibility predicate. -/
@[simp] theorem mem_feasibleSet (problem : FunctionalConstraintsMinimizationProblem X m)
    {x : problem.basicFeasibleSet} :
    x ∈ problem.feasibleSet ↔ problem.IsFeasible x :=
  Iff.rfl

section Optimality

variable [TopologicalSpace X]

/-- A local solution is equivalently described by a neighborhood within the feasible set on which
the objective is minimal. -/
theorem isLocalMinOn_iff_exists_set (problem : FunctionalConstraintsMinimizationProblem X m)
    {xStar : problem.feasibleSet} :
    IsLocalMinOn problem.objective problem.feasibleSet xStar ↔
      ∃ N : Set problem.basicFeasibleSet,
        N ∈ nhdsWithin (xStar : problem.basicFeasibleSet) problem.feasibleSet ∧
          IsMinOn problem.objective N xStar := by
  constructor
  · intro hx
    refine ⟨{x | problem.objective xStar ≤ problem.objective x}, ?_, ?_⟩
    · simpa [IsLocalMinOn, IsMinFilter] using hx
    · exact (isMinOn_iff).2 fun _ hx ↦ hx
  · rintro ⟨N, hN, hmin⟩
    rw [IsLocalMinOn, IsMinFilter]
    exact Filter.mem_of_superset hN <| by
      intro x hx
      exact (isMinOn_iff.mp hmin) x hx

/-- Definition 1.1.3: A feasible point is a strict local minimum when it is strictly better
than every distinct feasible point in some neighborhood inside the feasible set. -/
def IsStrictLocalMinimum (problem : FunctionalConstraintsMinimizationProblem X m)
    (xStar : problem.feasibleSet) : Prop :=
  ∃ N : Set problem.basicFeasibleSet,
    N ∈ nhdsWithin (xStar : problem.basicFeasibleSet) problem.feasibleSet ∧
      ∀ x : problem.basicFeasibleSet,
        x ∈ N → x ≠ xStar → problem.objective xStar < problem.objective x

/-- A strict local minimum is, in particular, a local minimum on the feasible set. -/
theorem IsStrictLocalMinimum.isLocalMinOn
    {xStar : problem.feasibleSet} (hx : problem.IsStrictLocalMinimum xStar) :
    IsLocalMinOn problem.objective problem.feasibleSet xStar := by
  rcases hx with ⟨N, hN, hstrict⟩
  rw [IsLocalMinOn, IsMinFilter]
  refine Filter.mem_of_superset hN ?_
  intro x hxN
  by_cases hx : x = xStar
  · simp [hx]
  · exact le_of_lt (hstrict x hxN hx)

end Optimality

end FunctionalConstraintsMinimizationProblem

/- Definition 1.1.3 lies in the order/topology domain of constrained optimization on a feasible
subtype.

Sampled owner-style declarations:
* `IsMinOn`
* `isMinOn_iff`
* `IsLocalMinOn`
* `GeneralMinimizationProblem` in this chapter

Owner abstraction:
* source-facing owner: `GeneralMinimizationProblem n m`
* bridge/generalization: `FunctionalConstraintsMinimizationProblem X m`

Primitive data:
* `basicFeasibleSet`
* `objective`
* `constraints`
* `senses`

Derived API:
* the shared feasibility predicate `problem.IsFeasible`
* the shared feasible set `problem.feasibleSet`
* the owner feasible-set rewrite `problem.mem_feasibleSet`
* global and local optimality as `IsMinOn` and `IsLocalMinOn` on `problem.feasibleSet`
* the local-set reformulation `problem.isLocalMinOn_iff_exists_set`
* the owner strict-local predicate `problem.IsStrictLocalMinimum`

Source/core/bridge triage:
* source-facing: the feasible-point optimality notions on `GeneralMinimizationProblem n m`
* core/canonical: `FunctionalConstraintsMinimizationProblem X m` together with its feasible-set
  and strict-local-minimum API
* bridge/view: `GeneralMinimizationProblem n m` as the textbook `ℝⁿ` specialization
-/

namespace GeneralMinimizationProblem

section Optimality

variable {n m : ℕ} {problem : GeneralMinimizationProblem n m} {xStar : problem.feasibleSet}

/- Definition 1.1.3 (1): a feasible point `xStar` is an optimal global solution exactly when
`IsMinOn problem.objective problem.feasibleSet xStar`. -/
#check IsMinOn problem.objective problem.feasibleSet xStar

/- Definition 1.1.3 (2): a feasible point `xStar` is a local solution exactly when
`IsLocalMinOn problem.objective problem.feasibleSet xStar`. -/
#check IsLocalMinOn problem.objective problem.feasibleSet xStar

/- Definition 1.1.3 (3): the strict local minimum notion is the owner-level predicate
`problem.IsStrictLocalMinimum xStar`. -/
#check problem.IsStrictLocalMinimum xStar

end Optimality

end GeneralMinimizationProblem
