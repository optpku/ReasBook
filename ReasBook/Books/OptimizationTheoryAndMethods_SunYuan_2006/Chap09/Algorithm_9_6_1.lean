/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Definition_9_1_extra_1

noncomputable section

open Matrix

section Chapter09Algorithm961

variable {n me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "pointEquiv" => EuclideanSpace.equiv (Fin n) ℝ

open scoped BigOperators

-- Domain-style sampling in Chapter 9:
-- * primary domain: quadratic programming with the Chapter 8 constrained-problem/KKT owner
--   available through `QuadraticProgram.toConstrainedOptimizationProblem`;
-- * inspected owner declarations: `QuadraticProgram.toConstrainedOptimizationProblem` from
--   `Definition_9_1_extra_1`, `ConstrainedOptimizationProblem.IsKKTPoint` from
--   `Theorem_8_2_7`, `QuadraticProgram.activeSet` / `workingSetFeasibleDirections` from
--   `Algorithm_9_4_2`, and the Chapter 9 second-order/KKT bridge usage in `Theorem_9_1_1`;
-- * best owner abstraction: the canonical KKT predicate lives on
--   `P.toConstrainedOptimizationProblem`, so this file should transport iterates to that owner
--   rather than declare another quadratic-program-level KKT predicate. Within the source-facing
--   Step-2 layer, the strict interior region should be owned by a set-valued declaration, with
--   pointwise predicates and subproblem certificates derived from that owner;
-- * primitive data vs. derived API: the primitive source-facing data here are the strict
--   interior set, the barrier objective, the Step-2 datum `xHat`, and the iterate/scaling data.
--   Pointwise strict interiority, the Step-2 subproblem predicate, and the Step-3 stopping test
--   are derived logical API.

namespace QuadraticProgram

/- Source-facing owner for the Step-2 domain of Algorithm 9.6.1. -/

/-- The strict interior region of `P` consists of the points satisfying the equality constraints
and all inequality constraints strictly. -/
def strictInteriorSet (P : QuadraticProgram n me mi) : Set Point :=
  {x | P.Aeq.mulVec x = P.beq ∧ ∀ i : Fin mi, P.bineq i < (P.Aineq.mulVec x) i}

/-- Membership in `P.strictInteriorSet` is exactly equality feasibility together with strict
inequality feasibility. -/
theorem mem_strictInteriorSet_iff
    (P : QuadraticProgram n me mi) (x : Point) :
    x ∈ P.strictInteriorSet ↔
      P.Aeq.mulVec x = P.beq ∧ ∀ i : Fin mi, P.bineq i < (P.Aineq.mulVec x) i :=
  Iff.rfl

/-- A strict interior point of `P` satisfies the equality constraints and all inequality
constraints strictly. -/
abbrev IsStrictInteriorPoint (P : QuadraticProgram n me mi) (x : Point) : Prop :=
  x ∈ P.strictInteriorSet

/-- Unfolding `P.IsStrictInteriorPoint x` gives the equality constraints together with strict
inequality feasibility. -/
theorem isStrictInteriorPoint_iff
    (P : QuadraticProgram n me mi) (x : Point) :
    P.IsStrictInteriorPoint x ↔
      P.Aeq.mulVec x = P.beq ∧ ∀ i : Fin mi, P.bineq i < (P.Aineq.mulVec x) i :=
  P.mem_strictInteriorSet_iff x

/-- The logarithmic-barrier objective used in the Step-2 subproblem of Algorithm 9.6.1. -/
def interiorEllipsoidBarrierObjective
    (P : QuadraticProgram n me mi) (mu : ℝ) (x : Point) : ℝ :=
  P.objective x - mu * ∑ i : Fin mi, Real.log ((P.Aineq.mulVec x) i - P.bineq i)

/-- The Step-2 datum `x̂(μ̂_k)` used by Algorithm 9.6.1, split into the first `n` coordinates
and the last coordinate appearing in `(9.6.35)`. -/
structure InteriorEllipsoidSubproblemPoint (n : ℕ) where
  primalPart : EuclideanSpace ℝ (Fin n)
  lastCoord : ℝ

/-- The Step-2 datum `xHat` solves the subproblem `(9.6.22)`-`(9.6.24)` for the barrier
parameter `μ` when its first `n` coordinates form a strict interior point minimizing the
logarithmic-barrier objective over the strict interior region of `P`, and its last coordinate is
positive for the update formula `(9.6.35)`. -/
def SolvesInteriorEllipsoidSubproblem
    (P : QuadraticProgram n me mi) (mu : ℝ)
    (xHat : InteriorEllipsoidSubproblemPoint n) : Prop :=
  P.IsStrictInteriorPoint xHat.primalPart ∧
    0 < xHat.lastCoord ∧
    IsMinOn
      (P.interiorEllipsoidBarrierObjective mu)
      P.strictInteriorSet
      xHat.primalPart

/-- A Step-2 subproblem solution has strictly interior primal part. -/
theorem SolvesInteriorEllipsoidSubproblem.strictInterior
    {P : QuadraticProgram n me mi} {mu : ℝ} {xHat : InteriorEllipsoidSubproblemPoint n}
    (h : P.SolvesInteriorEllipsoidSubproblem mu xHat) :
    P.IsStrictInteriorPoint xHat.primalPart :=
  h.1

/-- A Step-2 subproblem solution has positive last coordinate. -/
theorem SolvesInteriorEllipsoidSubproblem.lastCoord_pos
    {P : QuadraticProgram n me mi} {mu : ℝ} {xHat : InteriorEllipsoidSubproblemPoint n}
    (h : P.SolvesInteriorEllipsoidSubproblem mu xHat) :
    0 < xHat.lastCoord :=
  h.2.1

/-- A Step-2 subproblem solution minimizes the barrier objective on the strict interior region. -/
theorem SolvesInteriorEllipsoidSubproblem.isMinOn
    {P : QuadraticProgram n me mi} {mu : ℝ} {xHat : InteriorEllipsoidSubproblemPoint n}
    (h : P.SolvesInteriorEllipsoidSubproblem mu xHat) :
    IsMinOn
      (P.interiorEllipsoidBarrierObjective mu)
      P.strictInteriorSet
      xHat.primalPart :=
  h.2.2

/-- Unfolding `P.SolvesInteriorEllipsoidSubproblem μ xHat` gives the Step-2 strict-interior,
positive-last-coordinate, and barrier-minimization conditions. -/
theorem solvesInteriorEllipsoidSubproblem_iff
    (P : QuadraticProgram n me mi) (mu : ℝ)
    (xHat : InteriorEllipsoidSubproblemPoint n) :
    P.SolvesInteriorEllipsoidSubproblem mu xHat ↔
      P.IsStrictInteriorPoint xHat.primalPart ∧
        0 < xHat.lastCoord ∧
        IsMinOn
          (P.interiorEllipsoidBarrierObjective mu)
          P.strictInteriorSet
          xHat.primalPart :=
  Iff.rfl

end QuadraticProgram

open QuadraticProgram (InteriorEllipsoidSubproblemPoint)

/-- The Step-2 update formula `(9.6.35)` sends the scaling matrix `Dk` and the Step-2 datum
`xHat`, with first `n` coordinates `xHat.primalPart` and last coordinate `xHat.lastCoord`, to
`Dk xHat.primalPart / xHat.lastCoord`. -/
def interiorEllipsoidUpdate
    (Dk : Matrix (Fin n) (Fin n) ℝ)
    (xHat : InteriorEllipsoidSubproblemPoint n) : Point :=
  xHat.lastCoord⁻¹ • WithLp.toLp 2 (Dk.mulVec xHat.primalPart.ofLp)

/-- Unfolding `interiorEllipsoidUpdate Dk xHat` gives the exact Step-2 update formula
`(9.6.35)`. -/
theorem interiorEllipsoidUpdate_def
    (Dk : Matrix (Fin n) (Fin n) ℝ)
    (xHat : InteriorEllipsoidSubproblemPoint n) :
    interiorEllipsoidUpdate Dk xHat =
      xHat.lastCoord⁻¹ • WithLp.toLp 2 (Dk.mulVec xHat.primalPart.ofLp) :=
  rfl

/-- Chapter09 Algorithm 9.6.1: an interior ellipsoid method for the quadratic program `P`
records that `P` is convex, starts from a strict interior point `x1` of `(9.6.3)`-`(9.6.5)`
with `iterate 0 = x1`, and stores the Step-2 subproblem data together with the exact iterate
update formula `(9.6.35)` and the Step-3 KKT stop/continue rule. -/
structure InteriorEllipsoidMethod (P : QuadraticProgram n me mi) where
  convex : P.G.PosSemidef
  x1 : Point
  active : ℕ → Prop
  iterate : ℕ → Point
  muHat : ℕ → ℝ
  xHat : ℕ → InteriorEllipsoidSubproblemPoint n
  scalingMatrix : ℕ → Matrix (Fin n) (Fin n) ℝ
  active_zero : active 0
  iterate_zero : iterate 0 = x1
  x1_strictInterior : P.IsStrictInteriorPoint x1
  subproblem_solution :
    ∀ k : ℕ, active k → P.SolvesInteriorEllipsoidSubproblem (muHat k) (xHat k)
  iterate_succ :
    ∀ k : ℕ, active k →
      iterate (k + 1) = interiorEllipsoidUpdate (scalingMatrix k) (xHat k)
  active_succ_iff :
    ∀ k : ℕ,
      active (k + 1) ↔
        active k ∧
          ¬ ∃ lamStar : Fin (me + mi) → ℝ,
            P.toConstrainedOptimizationProblem.IsKKTPoint
              (pointEquiv (iterate (k + 1))) lamStar

/-- An interior ellipsoid method can be evaluated as its iterate sequence. -/
instance (P : QuadraticProgram n me mi) :
    CoeFun (InteriorEllipsoidMethod P) (fun _ ↦ ℕ → Point) where
  coe A := A.iterate

namespace InteriorEllipsoidMethod

/-- At each active stage, the last coordinate of the Step-2 datum `x̂(μ̂_(k+1))` used in
`(9.6.35)` is positive. -/
theorem lastCoord_pos
    {P : QuadraticProgram n me mi}
    (A : InteriorEllipsoidMethod P) (k : ℕ) (hactive : A.active k) :
    0 < (A.xHat k).lastCoord :=
  (A.subproblem_solution k hactive).lastCoord_pos

/-- The stopping condition in Chapter09 Algorithm 9.6.1 is that the fresh iterate produced at
stage `k` is a KKT point. -/
def terminatedAt
    {P : QuadraticProgram n me mi}
    (A : InteriorEllipsoidMethod P) (k : ℕ) : Prop :=
  ∃ lamStar : Fin (me + mi) → ℝ,
    P.toConstrainedOptimizationProblem.IsKKTPoint
      (pointEquiv (A.iterate (k + 1))) lamStar

/-- Unfolding `terminatedAt` gives the Step-3 KKT stopping test on the fresh iterate. -/
theorem terminatedAt_iff
    {P : QuadraticProgram n me mi}
    (A : InteriorEllipsoidMethod P) (k : ℕ) :
    A.terminatedAt k ↔
      ∃ lamStar : Fin (me + mi) → ℝ,
        P.toConstrainedOptimizationProblem.IsKKTPoint
          (pointEquiv (A.iterate (k + 1))) lamStar :=
  Iff.rfl

/-- If stage `k` is active, then Step 3 continues to stage `k + 1` exactly when the fresh
iterate `iterate (k + 1)` is not a KKT point of `P`. -/
theorem active_succ_iff_not_terminatedAt
    {P : QuadraticProgram n me mi}
    (A : InteriorEllipsoidMethod P) (k : ℕ) (hactive : A.active k) :
    A.active (k + 1) ↔ ¬ A.terminatedAt k := by
  simpa [InteriorEllipsoidMethod.terminatedAt, hactive] using A.active_succ_iff k

/-- Unfolding `InteriorEllipsoidMethod` gives the convexity of `P`, the Step-1 strict-interior
initialization, the Step-2 data `μ̂_k`, `x̂(μ̂_k)`, and `D_k` together with the exact iterate
update formula `(9.6.35)` on active stages, and the Step-3 KKT stop/continue rule from
Chapter09 Algorithm 9.6.1. -/
theorem spec
    {P : QuadraticProgram n me mi}
    (A : InteriorEllipsoidMethod P) :
    P.G.PosSemidef ∧
      A.active 0 ∧
      A.iterate 0 = A.x1 ∧
      P.IsStrictInteriorPoint A.x1 ∧
      (∀ k : ℕ, A.active k →
        P.SolvesInteriorEllipsoidSubproblem (A.muHat k) (A.xHat k)) ∧
      (∀ k : ℕ, A.active k →
        0 < (A.xHat k).lastCoord) ∧
      (∀ k : ℕ, A.active k →
        A.iterate (k + 1) = interiorEllipsoidUpdate (A.scalingMatrix k) (A.xHat k)) ∧
      (∀ k : ℕ, A.terminatedAt k ↔
        ∃ lamStar : Fin (me + mi) → ℝ,
          P.toConstrainedOptimizationProblem.IsKKTPoint
            (pointEquiv (A.iterate (k + 1))) lamStar) ∧
      (∀ k : ℕ, A.active (k + 1) ↔ A.active k ∧ ¬ A.terminatedAt k) := by
  refine ⟨A.convex, A.active_zero, A.iterate_zero, A.x1_strictInterior, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hactive
    exact A.subproblem_solution k hactive
  · intro k hactive
    exact A.lastCoord_pos k hactive
  · intro k hactive
    exact A.iterate_succ k hactive
  · intro k
    exact A.terminatedAt_iff k
  · intro k
    simpa [InteriorEllipsoidMethod.terminatedAt] using A.active_succ_iff k

end InteriorEllipsoidMethod

end Chapter09Algorithm961
