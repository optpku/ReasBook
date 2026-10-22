/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_1

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

-- Domain sampling:
-- * project owner: `ConstrainedOptimizationProblem` in `Definition_8_1_1`
-- * mathlib owner: `IsMinOn` and `isMinOn_iff`
-- * project owner for strict minima on a set: `IsStrictMinOn` and `isStrictMinOn_iff` in
--   `Chapter01.Definition_1_4_2`
-- Layer triage:
-- * source-facing: `ConstrainedOptimizationProblem`
-- * core/canonical: `IsMinOn` for non-strict minima and `IsStrictMinOn` for strict minima on
--   the feasible set
-- * bridge/view: `problem.IsGlobalMinimizer xStar`

/-- Chapter08 Definition 8.1.2 (1): `xStar` is a global minimizer of a constrained optimization
problem when it is feasible and minimizes the objective on the feasible set. -/
class ConstrainedOptimizationProblem.IsGlobalMinimizer
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (xStar : Point) : Prop where
  feasible : xStar ∈ problem
  isMinOn : IsMinOn problem.objective problem.feasibleSet xStar

/-- Proofs of `problem.IsGlobalMinimizer xStar` are propositionally unique. -/
instance instSubsingletonIsGlobalMinimizer
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (xStar : Point) :
    Subsingleton (problem.IsGlobalMinimizer xStar) :=
  inferInstance

/-- A constrained global minimizer compares below every feasible objective value. -/
theorem ConstrainedOptimizationProblem.IsGlobalMinimizer.objective_le
    {problem : _root_.ConstrainedOptimizationProblem n m E I} {xStar x : Point}
    (h : problem.IsGlobalMinimizer xStar) (hx : x ∈ problem) :
    problem.objective xStar ≤ problem.objective x :=
  (isMinOn_iff.mp h.isMinOn) x hx

/-- A constrained global minimizer is exactly a feasible point that minimizes the objective on the
feasible set. -/
theorem ConstrainedOptimizationProblem.isGlobalMinimizer_iff
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (xStar : Point) :
    problem.IsGlobalMinimizer xStar ↔
      xStar ∈ problem ∧ IsMinOn problem.objective problem.feasibleSet xStar := by
  constructor
  · intro h
    exact ⟨h.feasible, h.isMinOn⟩
  · rintro ⟨hfeasible, hisMinOn⟩
    exact ⟨hfeasible, hisMinOn⟩

/- Chapter08 Definition 8.1.2 (2): `xStar` is a strict global minimizer of a constrained
optimization problem precisely when it is a strict minimizer of the objective on the feasible set.
This is a direct recall of the Chapter 1 owner `IsStrictMinOn`, not a second local owner. -/
/- The strict constrained notion is the canonical Chapter 1 owner
`IsStrictMinOn problem.objective problem.feasibleSet xStar`; this file only adds thin bridge API
back to constrained minimizers. -/
#check fun (problem : _root_.ConstrainedOptimizationProblem n m E I) (xStar : Point) ↦
  IsStrictMinOn problem.objective problem.feasibleSet xStar

/-- A strict constrained minimizer is, in particular, a constrained global minimizer. -/
instance instIsGlobalMinimizerOfIsStrictMinOn
    {problem : _root_.ConstrainedOptimizationProblem n m E I} {xStar : Point}
    [h : IsStrictMinOn problem.objective problem.feasibleSet xStar] :
    problem.IsGlobalMinimizer xStar where
  feasible := h.mem
  isMinOn := h.isMinOn

/-- A strict constrained minimizer is, in particular, a constrained global minimizer. -/
theorem IsStrictMinOn.isGlobalMinimizer
    {problem : _root_.ConstrainedOptimizationProblem n m E I} {xStar : Point}
    (h : IsStrictMinOn problem.objective problem.feasibleSet xStar) :
    problem.IsGlobalMinimizer xStar :=
  ⟨h.mem, h.isMinOn⟩

/-- Chapter08 Definition 8.1.2 (2): specializing `IsStrictMinOn` to the feasible set gives the
usual constrained strict global minimizer condition. -/
theorem ConstrainedOptimizationProblem.isStrictGlobalMinimizer_iff
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (xStar : Point) :
    IsStrictMinOn problem.objective problem.feasibleSet xStar ↔
      xStar ∈ problem ∧
        ∀ x : Point,
          x ∈ problem → x ≠ xStar → problem.objective xStar < problem.objective x := by
  rw [isStrictMinOn_iff]
  constructor
  · rintro ⟨hxStar, hstrict⟩
    refine ⟨hxStar, ?_⟩
    intro x hx hne
    exact hstrict x hx hne
  · rintro ⟨hxStar, hstrict⟩
    refine ⟨hxStar, ?_⟩
    intro x hx hne
    exact hstrict x hx hne
