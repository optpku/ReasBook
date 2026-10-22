/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Theorem_10_6_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Theorem_12_1_2

open Filter
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => LagrangeNewtonPoint n
local notation "Multiplier" => LagrangeNewtonMultiplier m
local notation "Method" => _root_.LagrangeNewtonMethod Point Multiplier
local notation "HessianMatrix" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling:
-- * source-facing layer: the equality-constrained KKT conclusion of Theorem 12.1.3 and the
--   theorem-local uniform bound on the stagewise KKT matrices
-- * core/canonical layer already in the repository:
--   `EqualityConstrainedProblem` from `Chapter12.EqualityConstrainedProblem` and
--   `LagrangeNewtonMethod` together with the bridge predicate `LagrangeNewtonMethod.IsFor`
--   from `Theorem_12_1_2`
-- * bridge/view layer here:
--   the source-facing comparison theorems from `problem.IsKKTPoint` to the canonical Chapter 8
--   and Chapter 10 KKT owners on the equality-only bridge
--   `problem.toStandardPenaltyProblem`

namespace EqualityConstrainedProblem

/-- The source-facing equality-constrained KKT owner is equivalent to the canonical Chapter 8
KKT owner on the Chapter 10 equality-only bridge
`problem.toStandardPenaltyProblem.toConstrainedOptimizationProblem`. -/
theorem isKKTPoint_iff_toConstrainedOptimizationProblem_isKKTPoint
    (problem : EqualityConstrainedProblem n m) (xStar : Point) (lamStar : Multiplier) :
    problem.IsKKTPoint xStar lamStar ↔
      let constrainedProblem := problem.toStandardPenaltyProblem.toConstrainedOptimizationProblem
      constrainedProblem.IsKKTPoint xStar.ofLp lamStar.ofLp := by
  sorry

/-- For an equality-constrained problem, the Chapter 10 Lagrange-multiplier owner on the
equality-only bridge `problem.toStandardPenaltyProblem` recovers the native Chapter 12 KKT
owner `problem.IsKKTPoint`. -/
theorem isKKTPoint_of_toStandardPenaltyProblem_isLagrangeMultiplier
    {problem : EqualityConstrainedProblem n m} {xStar : Point} {lamStar : Multiplier}
    (h : problem.toStandardPenaltyProblem.IsLagrangeMultiplier xStar lamStar) :
    problem.IsKKTPoint xStar lamStar := by
  exact
    (problem.isKKTPoint_iff_toConstrainedOptimizationProblem_isKKTPoint xStar lamStar).2
      h.toIsKKTPoint

/-- An equality-constrained KKT point gives the canonical Chapter 10 Lagrange-multiplier owner
on the equality-only bridge as soon as the Euclidean Lagrangian is differentiable at the
point. -/
theorem IsKKTPoint.toIsLagrangeMultiplier
    {problem : EqualityConstrainedProblem n m} {xStar : Point} {lamStar : Multiplier}
    (h : problem.IsKKTPoint xStar lamStar)
    (hLagrangianDifferentiableAt :
      DifferentiableAt ℝ (fun x : Point ↦ problem.lagrangian x lamStar) xStar) :
    problem.toStandardPenaltyProblem.IsLagrangeMultiplier xStar lamStar := by
  exact
    ⟨(problem.isKKTPoint_iff_toConstrainedOptimizationProblem_isKKTPoint xStar lamStar).1 h,
      hLagrangianDifferentiableAt⟩

/-- Under the global `C¹` assumptions used later in Chapter 12, an equality-constrained KKT
point yields the Chapter 10 Lagrange-multiplier owner for the equality-only bridge
`problem.toStandardPenaltyProblem`. This is a thin `ContDiff` companion to the primitive
differentiability bridge `problem.IsKKTPoint.toIsLagrangeMultiplier`. -/
theorem IsKKTPoint.toIsLagrangeMultiplier_of_contDiff
    {problem : EqualityConstrainedProblem n m} {xStar : Point} {lamStar : Multiplier}
    (h : problem.IsKKTPoint xStar lamStar)
    (hObjectiveC1 : ContDiff ℝ 1 problem.objective)
    (hConstraintC1 : ∀ i : Fin m, ContDiff ℝ 1 (problem.constraint i))
    : problem.toStandardPenaltyProblem.IsLagrangeMultiplier xStar lamStar := by
  refine h.toIsLagrangeMultiplier ?_
  sorry

end EqualityConstrainedProblem

namespace LagrangeNewtonMethod

/-- `method.HasUniformlyBoundedKKTMatrix` means that the source KKT matrices `(12.1.12)` along
the Algorithm 12.1.1 stages `k ≥ 1` are bounded in norm by one common constant. -/
def HasUniformlyBoundedKKTMatrix
    (method : Method)
    (problem : EqualityConstrainedProblem n m)
    (W : Point → Multiplier → HessianMatrix) : Prop :=
  ∃ bound : ℝ, 0 ≤ bound ∧ ∀ k : ℕ, 1 ≤ k → ‖method.kktMatrixAt problem W k‖ ≤ bound

/-- Unfolding `method.HasUniformlyBoundedKKTMatrix` gives a common norm bound for the source KKT
matrices `(12.1.12)` along the stages `k ≥ 1`. -/
theorem hasUniformlyBoundedKKTMatrix_iff
    (method : Method)
    (problem : EqualityConstrainedProblem n m)
    (W : Point → Multiplier → HessianMatrix) :
    method.HasUniformlyBoundedKKTMatrix problem W ↔
      ∃ bound : ℝ, 0 ≤ bound ∧ ∀ k : ℕ, 1 ≤ k → ‖method.kktMatrixAt problem W k‖ ≤ bound :=
  Iff.rfl

end LagrangeNewtonMethod

/-- Chapter12 Theorem 12.1.3: assume `problem.objective` and every component of
`problem.constraint` are twice continuously differentiable. If the KKT matrix `(12.1.12)` along
the Algorithm 12.1.1 sequence generated by the canonical owner `method`, whose Step-2
equation and merit-function root condition are related to `problem` by
`hMethod : method.IsFor problem W`, is uniformly bounded, then every accumulation point of the
primal iterate sequence `{x_k}` is a KKT point of the equality-constrained problem
`(12.1.1)`-`(12.1.2)`. The accumulation-point hypothesis is encoded by a strictly monotone
subsequence of the source stages `k ≥ 1` converging to `xStar`. -/
theorem lagrangeNewton_accumulationPoint_isKKTPoint
    (problem : EqualityConstrainedProblem n m)
    (method : Method)
    (W : Point → Multiplier → HessianMatrix)
    (hMethod : method.IsFor problem W)
    (hObjectiveC2 : ContDiff ℝ 2 problem.objective)
    (hConstraintC2 : ∀ i : Fin m, ContDiff ℝ 2 (problem.constraint i))
    (hKKTBound : method.HasUniformlyBoundedKKTMatrix problem W)
    {xStar : Point} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxStar : Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xStar)) :
    ∃ lamStar : Multiplier, problem.IsKKTPoint xStar lamStar := by
  sorry

end
