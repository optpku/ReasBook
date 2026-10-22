/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.Module.LinearMap.Defs
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_1

section Chapter08Definition828

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

namespace ConstrainedOptimizationProblem

/-- Chapter08 Definition 8.2.8: linear function constraint qualification (LFCQ) holds at `xStar`
when every active constraint of `problem` at `xStar` is a linear function. -/
class LfcqAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point) : Prop where
  /-- Every active constraint of `problem` at `xStar` is represented by a linear map. -/
  constraint_eq_linearMap (i : Fin m) (hi : i ∈ problem.activeConstraintIndexSet xStar) :
    ∃ ci : Point →ₗ[ℝ] ℝ, problem.constraint i = ci

/-- `problem.LfcqAt xStar` is a proposition. -/
instance instSubsingletonLfcqAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point) :
    Subsingleton (problem.LfcqAt xStar) :=
  inferInstance

/-- Unfolding formula for `problem.LfcqAt xStar`. -/
theorem lfcqAt_iff
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point) :
    problem.LfcqAt xStar ↔
      ∀ i : Fin m, i ∈ problem.activeConstraintIndexSet xStar →
        ∃ ci : Point →ₗ[ℝ] ℝ, problem.constraint i = ci :=
  ⟨fun h i hi ↦ h.constraint_eq_linearMap i hi, fun h ↦
    ⟨fun i hi ↦ h i hi⟩⟩

/-- Under `problem.LfcqAt xStar`, each active constraint at `xStar` is represented by a linear
map. -/
theorem LfcqAt.constraint_eq_linearMap_of_mem
    {problem : ConstrainedOptimizationProblem n m E I} {xStar : Point} {i : Fin m}
    (h_lfcq : problem.LfcqAt xStar) (hi : i ∈ problem.activeConstraintIndexSet xStar) :
    ∃ ci : Point →ₗ[ℝ] ℝ, problem.constraint i = ci :=
  h_lfcq.constraint_eq_linearMap i hi

end ConstrainedOptimizationProblem

end Chapter08Definition828
