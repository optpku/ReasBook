/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_2

noncomputable section

section Chapter08Definition8210

variable {n m : ℕ} {E I : Set (Fin m)}

-- Domain sampling:
-- * primary domain: LICQ for constrained optimization problems
-- * inspected owners:
--   `ConstrainedOptimizationProblem.activeConstraintIndexSet` from `Definition_8_1_1`
--   `ConstrainedOptimizationProblem.HasActiveConstraintGradientsAt` from `Definition_8_2_2`
--   mathlib's `LinearIndepOn`
--   `StandardPenaltyProblem.LicqAt` from Chapter 10
-- * owner abstraction chosen here:
--   `source-facing`: `problem.LicqAt xStar`
--   `core/canonical`: `LinearIndepOn`
--   `bridge/view`: `problem.euclideanConstraint` and `WithLp.toLp 2 xStar` for mathlib's
--   Euclidean gradient API
-- * primitive data vs derived API:
--   the primitive fields are active-constraint differentiability and active-gradient linear
--   independence; pointwise differentiability of a single active constraint is derived

namespace ConstrainedOptimizationProblem

local notation "Point" => Fin n → ℝ

/-- Chapter08 Definition 8.2.10: LICQ holds at `xStar` when every active constraint of
`problem` is differentiable at `xStar` and the active-constraint gradients are linearly
independent. The gradients are evaluated on the Euclidean transport already used by the chapter's
gradient API. -/
@[mk_iff licqAt_iff]
class LicqAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point) : Prop where
  /-- Every active constraint of `problem` is differentiable at `xStar`. -/
  hasActiveConstraintGradientsAt : problem.HasActiveConstraintGradientsAt xStar
  /-- The active-constraint gradients are linearly independent. -/
  linearIndepOn :
    LinearIndepOn ℝ
      (fun i : Fin m ↦ gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar))
      (problem.activeConstraintIndexSet xStar)

attribute [simp] licqAt_iff

/-- Under `problem.LicqAt xStar`, each active constraint of `problem` is differentiable at
`xStar`. -/
theorem LicqAt.differentiableAt_of_mem
    {problem : ConstrainedOptimizationProblem n m E I} {xStar : Point} {i : Fin m}
    (h_licq : problem.LicqAt xStar) (hi : i ∈ problem.activeConstraintIndexSet xStar) :
    DifferentiableAt ℝ (problem.constraint i) xStar :=
  h_licq.hasActiveConstraintGradientsAt i hi

end ConstrainedOptimizationProblem

end Chapter08Definition8210
