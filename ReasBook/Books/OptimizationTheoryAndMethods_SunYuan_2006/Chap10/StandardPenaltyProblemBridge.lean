/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_10
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_1_extra_1

noncomputable section

section Chapter10StandardPenaltyProblemBridge

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

namespace StandardPenaltyProblem

/-- The equality-constraint index set determined by `problem.eqCount`. -/
def eqIndices (problem : StandardPenaltyProblem n m) : Set (Fin m) :=
  {i | i.1 < problem.eqCount}

/-- The inequality-constraint index set determined by `problem.eqCount`. -/
def ineqIndices (problem : StandardPenaltyProblem n m) : Set (Fin m) :=
  {i | problem.eqCount ≤ i.1}

@[simp] theorem mem_eqIndices_iff (problem : StandardPenaltyProblem n m) (i : Fin m) :
    i ∈ problem.eqIndices ↔ i.1 < problem.eqCount :=
  Iff.rfl

@[simp] theorem mem_ineqIndices_iff (problem : StandardPenaltyProblem n m) (i : Fin m) :
    i ∈ problem.ineqIndices ↔ problem.eqCount ≤ i.1 :=
  Iff.rfl

/-- The contiguous equality/inequality split determined by `eqCount` covers all indices. -/
theorem eqIndices_union_ineqIndices (problem : StandardPenaltyProblem n m) :
    problem.eqIndices ∪ problem.ineqIndices = Set.univ := by
  ext i
  simp [eqIndices, ineqIndices, Nat.lt_or_ge]

/-- The equality and inequality index blocks determined by `eqCount` are disjoint. -/
theorem eqIndices_disjoint_ineqIndices (problem : StandardPenaltyProblem n m) :
    Disjoint problem.eqIndices problem.ineqIndices := by
  refine Set.disjoint_left.2 fun i hi_eq hi_ineq ↦ ?_
  exact (Nat.not_lt_of_ge hi_ineq) hi_eq

/-- The canonical Chapter 8 constrained-optimization view of a mixed-constraint
`StandardPenaltyProblem`. -/
def toConstrainedOptimizationProblem (problem : StandardPenaltyProblem n m) :
    _root_.ConstrainedOptimizationProblem n m problem.eqIndices problem.ineqIndices where
  objective := fun x ↦ problem.objective (WithLp.toLp 2 x)
  constraint := fun i x ↦ problem.constraint i (WithLp.toLp 2 x)
  eqIndices_union_ineqIndices := problem.eqIndices_union_ineqIndices
  eqIndices_disjoint_ineqIndices := problem.eqIndices_disjoint_ineqIndices

@[simp] theorem toConstrainedOptimizationProblem_objective_apply
    (problem : StandardPenaltyProblem n m) (x : Point) :
    problem.toConstrainedOptimizationProblem.objective x.ofLp = problem.objective x := by
  simp [toConstrainedOptimizationProblem]

@[simp] theorem toConstrainedOptimizationProblem_constraint_apply
    (problem : StandardPenaltyProblem n m) (i : Fin m) (x : Point) :
    problem.toConstrainedOptimizationProblem.constraint i x.ofLp = problem.constraint i x := by
  simp [toConstrainedOptimizationProblem]

/-- Active inequality indices of the Chapter 8 bridge are exactly the mixed inequality
constraints with zero value. -/
@[simp] theorem mem_activeIneqIndexSet_toConstrainedOptimizationProblem_iff
    (problem : StandardPenaltyProblem n m) (x : Point) (i : Fin m) :
    i ∈
        problem.toConstrainedOptimizationProblem.activeIneqIndexSet x.ofLp ↔
      problem.eqCount ≤ i.1 ∧ problem.constraint i x = 0 := by
  constructor
  · intro hi
    rw [ConstrainedOptimizationProblem.mem_activeIneqIndexSet_iff] at hi
    rcases hi with ⟨hineq, hzero⟩
    refine ⟨?_, ?_⟩
    · simpa [ConstrainedOptimizationProblem.ineqIndices, StandardPenaltyProblem.ineqIndices]
        using hineq
    · simpa [toConstrainedOptimizationProblem] using hzero
  · rintro ⟨hineq, hzero⟩
    rw [ConstrainedOptimizationProblem.mem_activeIneqIndexSet_iff]
    refine ⟨?_, ?_⟩
    · simpa [ConstrainedOptimizationProblem.ineqIndices, StandardPenaltyProblem.ineqIndices]
        using hineq
    · simpa [toConstrainedOptimizationProblem] using hzero

/-- The active constraints at `xStar` are all equality constraints together with the inequality
constraints that satisfy `cᵢ(xStar) = 0`, viewed through the canonical Chapter 8 active-set
owner on `problem.toConstrainedOptimizationProblem`. -/
abbrev activeConstraintSet
    (problem : StandardPenaltyProblem n m) (xStar : Point) : Set (Fin m) :=
  problem.toConstrainedOptimizationProblem.activeConstraintIndexSet xStar.ofLp

/-- Membership in `problem.activeConstraintSet xStar` means that `i` is either an equality
constraint index or an active inequality index at `xStar`. -/
theorem mem_activeConstraintSet_iff
    (problem : StandardPenaltyProblem n m) (xStar : Point) (i : Fin m) :
    i ∈ problem.activeConstraintSet xStar ↔
      i.1 < problem.eqCount ∨
        problem.eqCount ≤ i.1 ∧ problem.constraint i xStar = 0 := by
  rw [ConstrainedOptimizationProblem.mem_activeConstraintIndexSet_iff]
  constructor
  · rintro (hi_eq | ⟨hi_ineq, hzero⟩)
    · left
      simpa [ConstrainedOptimizationProblem.eqIndices, StandardPenaltyProblem.eqIndices] using hi_eq
    · right
      refine ⟨?_, ?_⟩
      · simpa [ConstrainedOptimizationProblem.ineqIndices, StandardPenaltyProblem.ineqIndices]
          using hi_ineq
      · simpa using hzero
  · rintro (hi_eq | ⟨hi_ineq, hzero⟩)
    · left
      simpa [ConstrainedOptimizationProblem.eqIndices, StandardPenaltyProblem.eqIndices] using hi_eq
    · right
      refine ⟨?_, ?_⟩
      · simpa [ConstrainedOptimizationProblem.ineqIndices, StandardPenaltyProblem.ineqIndices]
          using hi_ineq
      · simpa using hzero

/-- LICQ at `xStar` for a mixed-constraint Chapter 10 problem is the canonical Chapter 8 LICQ
owner transported across `problem.toConstrainedOptimizationProblem`. -/
abbrev LicqAt (problem : StandardPenaltyProblem n m) (xStar : Point) : Prop :=
  problem.toConstrainedOptimizationProblem.LicqAt xStar.ofLp

/-- Feasibility of `x` for `problem` is equivalent to feasibility of `x.ofLp` for the canonical
Chapter 8 constrained-problem bridge. -/
theorem mem_toConstrainedOptimizationProblem_iff
    (problem : StandardPenaltyProblem n m) (x : Point) :
    x.ofLp ∈ problem.toConstrainedOptimizationProblem ↔ x ∈ problem := by
  change
      ((∀ i : Fin m,
          i ∈ problem.eqIndices →
            problem.toConstrainedOptimizationProblem.constraint i x.ofLp = 0) ∧
        ∀ i : Fin m,
          i ∈ problem.ineqIndices →
            0 ≤ problem.toConstrainedOptimizationProblem.constraint i x.ofLp) ↔
      ((∀ i : Fin m, i.1 < problem.eqCount → problem.constraint i x = 0) ∧
        ∀ i : Fin m, problem.eqCount ≤ i.1 → 0 ≤ problem.constraint i x)
  simp [eqIndices, ineqIndices]

/-- A mixed-constraint global minimizer is the Chapter 8 constrained global minimizer owner
transported along `problem.toConstrainedOptimizationProblem`. -/
abbrev IsGlobalMinimizer (problem : StandardPenaltyProblem n m) (xStar : Point) : Prop :=
  problem.toConstrainedOptimizationProblem.IsGlobalMinimizer xStar.ofLp

/-- Unfolding `problem.IsGlobalMinimizer xStar` gives feasibility together with minimization of
`problem.objective` on `problem.feasibleSet`. -/
theorem isGlobalMinimizer_iff
    (problem : StandardPenaltyProblem n m) (xStar : Point) :
    problem.IsGlobalMinimizer xStar ↔
      xStar ∈ problem.feasibleSet ∧ IsMinOn problem.objective problem.feasibleSet xStar := by
  constructor
  · intro h
    refine ⟨(problem.mem_toConstrainedOptimizationProblem_iff xStar).1 h.feasible, ?_⟩
    rw [isMinOn_iff]
    intro x hx
    have hx' : x.ofLp ∈ problem.toConstrainedOptimizationProblem :=
      (problem.mem_toConstrainedOptimizationProblem_iff x).2 hx
    simpa using h.objective_le hx'
  · rintro ⟨hxStar, hMin⟩
    refine ⟨(problem.mem_toConstrainedOptimizationProblem_iff xStar).2 hxStar, ?_⟩
    rw [isMinOn_iff]
    intro x hx
    have hx' : WithLp.toLp 2 x ∈ problem.feasibleSet := by
      have hx'' : (WithLp.toLp 2 x).ofLp ∈ problem.toConstrainedOptimizationProblem := by
        simpa [ConstrainedOptimizationProblem.feasibleSet_eq_setOf_mem] using hx
      exact (problem.mem_toConstrainedOptimizationProblem_iff (WithLp.toLp 2 x)).1 hx''
    change problem.objective xStar ≤ problem.objective (WithLp.toLp 2 x)
    exact (isMinOn_iff.mp hMin) (WithLp.toLp 2 x) hx'

/-- A Chapter 10 mixed-constraint global minimizer is feasible for `problem`. -/
theorem IsGlobalMinimizer.feasible
    {problem : StandardPenaltyProblem n m} {xStar : Point}
    (h : problem.IsGlobalMinimizer xStar) :
    xStar ∈ problem.feasibleSet :=
  (problem.isGlobalMinimizer_iff xStar).1 h |>.1

/-- A Chapter 10 mixed-constraint global minimizer minimizes `problem.objective` on
`problem.feasibleSet`. -/
theorem IsGlobalMinimizer.isMinOn
    {problem : StandardPenaltyProblem n m} {xStar : Point}
    (h : problem.IsGlobalMinimizer xStar) :
    IsMinOn problem.objective problem.feasibleSet xStar :=
  (problem.isGlobalMinimizer_iff xStar).1 h |>.2

/-- A mixed-constraint global minimizer compares below every feasible objective value. -/
theorem IsGlobalMinimizer.objective_le
    {problem : StandardPenaltyProblem n m} {xStar x : Point}
    (h : problem.IsGlobalMinimizer xStar) (hx : x ∈ problem.feasibleSet) :
    problem.objective xStar ≤ problem.objective x :=
  (isMinOn_iff.mp h.isMinOn) x hx

end StandardPenaltyProblem

end Chapter10StandardPenaltyProblemBridge
