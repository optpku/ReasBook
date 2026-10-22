/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_1_3

noncomputable section

section Chapter09Exercise92

variable {n me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "pointEquiv" => EuclideanSpace.equiv (Fin n) ℝ

/-!
Chapter09 Exercise 9.2

Domain sampling:
* primary domain: quadratic-program KKT and critical-cone second-order conditions;
* inspected project declarations:
  `QuadraticProgram` from `Chapter09.Definition_9_1_extra_1`,
  `QuadraticProgram.isLocalMinOn_iff_exists_isKKTPoint_with_secondOrderNecessaryCondition`
  from `Chapter09.Theorem_9_1_3`,
  `ConstrainedOptimizationProblem.IsKKTPoint` from `Chapter08.Theorem_8_2_7`,
  and `QuadraticProgram.HasSecondOrderNecessaryCondition` from `Chapter09.Theorem_9_1_1`;
* source/core/bridge triage:
  - source-facing owner reused here: the Chapter 9 local-optimality theorem
    surface from `Theorem_9_1_3`;
  - core/canonical layer sampled upstream in the chapter: the matrix-based
    owner `Definition_9_1_extra_1`, the Chapter 8 KKT owner, and the Chapter 9
    second-order owner from `Theorem_9_1_1`;
  - this exercise file remains a source-facing companion theorem, keeping only
    the forward implication needed for Exercise 9.2;
* primitive data vs derived API:
  - primitive/source-facing data already owned upstream: the quadratic-program
    object and feasible set, together with the canonical KKT and second-order
    owners;
  - derived API kept here: only the exercise-level implication extracted from
    the stronger iff theorem.
-/

/-- Chapter09 Exercise 9.2: if `xStar` is a feasible local minimizer of the
quadratic program `P`, then there exists a multiplier vector `λ*` such that
`(xStar, λ*)` is a Chapter 8 KKT pair for the constrained-problem bridge of
`P` and the Chapter 9 second-order necessary condition holds. -/
theorem localMinimizer_has_isKKTPoint_with_secondOrderNecessaryCondition
    (P : QuadraticProgram n me mi) (xStar : Point)
    (hLocalMin : IsLocalMinOn P P.feasibleSet xStar)
    (hxStar : xStar ∈ P.feasibleSet)
    ∃ lamStar : Fin (me + mi) → ℝ,
      P.toConstrainedOptimizationProblem.IsKKTPoint (pointEquiv xStar) lamStar ∧
        P.HasSecondOrderNecessaryCondition xStar lamStar :=
  (P.isLocalMinOn_iff_exists_isKKTPoint_with_secondOrderNecessaryCondition xStar hxStar).1
    hLocalMin

end Chapter09Exercise92
