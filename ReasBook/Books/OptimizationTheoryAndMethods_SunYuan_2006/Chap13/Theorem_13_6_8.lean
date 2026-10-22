/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Algorithm_13_6_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Lemma_13_6_4

noncomputable section

open Filter
open scoped Matrix PowellYuan1364

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "Jacobian" => Matrix (Fin n) (Fin m) ℝ
local notation "HessianApproximation" => Matrix (Fin n) (Fin n) ℝ
local notation "Method" => @PowellYuanTrustRegionMethod m n

-- Domain sampling pass:
-- * primary domain: Powell-Yuan global convergence alternatives in Chapter 13
-- * inspected declarations:
--   `PowellYuanTrustRegionMethod` from `Algorithm_13_6_1`
--   `PowellYuanTrustRegionMethod.satisfiesAssumption1362`
--   `PowellYuanTrustRegionMethod.finitelyTerminates`
--   `powellYuanProjector` from `Lemma_13_6_4`
-- * owner abstraction: `PowellYuanTrustRegionMethod`
-- * source/core/bridge triage:
--   - source-facing: the projected-gradient residual alternative of Theorem 13.6.8
--   - core/canonical: the method owner `PowellYuanTrustRegionMethod`
--   - bridge/view: the stagewise specialization of the canonical projector owner
--     `powellYuanProjector`
-- * primitive data vs derived API:
--   - primitive data: the recorded method run
--   - derived API: the stagewise bridge `projectedGradientProjectorAt`, the source residual
--     `projectedGradientResidualAt`, and the convergence/termination theorems

/-- The stagewise projector from `(13.6.58)` is the canonical owner
`powellYuanProjector` from Lemma 13.6.4 applied to `A_k`. -/
abbrev PowellYuanTrustRegionMethod.projectedGradientProjectorAt
    (method : Method) (k : ℕ) : HessianApproximation :=
  P̄[method.constraintJacobian k]

namespace PowellYuanTrustRegionMethod

/-- Unfolding `method.projectedGradientProjectorAt k` recovers the canonical owner
`P̄[A_k]`. -/
theorem projectedGradientProjectorAt_eq
    (method : Method) (k : ℕ) :
    method.projectedGradientProjectorAt k =
      P̄[method.constraintJacobian k] := rfl

/-- The source residual `(13.6.58)` evaluated at stage `k` is
`‖c_k‖ + ‖P̄_k g_k‖`, using the canonical projector
`P̄_k = I - A_k (A_k)⁺`. -/
def projectedGradientResidualAt (method : Method) (k : ℕ) : ℝ :=
  ‖method.constraintResidual k‖ +
    ‖Matrix.toEuclideanLin (method.projectedGradientProjectorAt k) (method.gradient k)‖

/-- Unfolding `method.projectedGradientResidualAt k` gives the source residual
`‖c_k‖ + ‖P̄_k g_k‖`. -/
theorem projectedGradientResidualAt_eq
    (method : Method) (k : ℕ) :
    method.projectedGradientResidualAt k =
      ‖method.constraintResidual k‖ +
        ‖Matrix.toEuclideanLin (method.projectedGradientProjectorAt k) (method.gradient k)‖ := rfl

/-- If a stagewise family `Pbar` agrees with the canonical projector
`P̄_k = I - A_k (A_k)⁺` at stage `k`, then the source residual rewrites to
`‖c_k‖ + ‖P̄_k g_k‖`. -/
theorem projectedGradientResidualAt_eq_of_projector_eq
    (method : Method) (Pbar : ℕ → HessianApproximation) {k : ℕ}
    (hPbar : Pbar k = method.projectedGradientProjectorAt k) :
    method.projectedGradientResidualAt k =
      ‖method.constraintResidual k‖ +
        ‖Matrix.toEuclideanLin (Pbar k) (method.gradient k)‖ := by
  rw [projectedGradientResidualAt_eq, hPbar]

/-- Chapter13 Theorem 13.6.8: under Chapter13 Assumption 13.6.2, either the Powell-Yuan
direction vanishes at some stage `k ≥ 1` or the source residual from `(13.6.58)`,
with the canonical projector `P̄_k = I - A_k (A_k)⁺`, satisfies
`liminf_(k → ∞) (‖c_k‖ + ‖P̄_k g_k‖) = 0`, encoded on the shifted sequence
`k ↦ method.projectedGradientResidualAt (k + 1)`. -/
theorem direction_zero_or_liminf_projectedGradientResidual_eq_zero_of_satisfiesAssumption1362
    (method : Method)
    (h1362 : method.satisfiesAssumption1362) :
    (∃ k : ℕ, 1 ≤ k ∧ method.direction k = 0) ∨
      Filter.liminf
          (fun k : ℕ ↦ method.projectedGradientResidualAt (k + 1))
          Filter.atTop = 0 := sorry

/-- If some stage `k ≥ 1` has zero search direction and such stages satisfy the recorded
Step-2 stopping test, then the recorded Algorithm 13.6.1 run terminates finitely. -/
theorem finitelyTerminates_of_exists_direction_zero
    (method : Method)
    (hDirectionZeroTerminated :
      ∀ k : ℕ, 1 ≤ k → method.direction k = 0 → method.terminatedAt k)
    (hZeroDirection : ∃ k : ℕ, 1 ≤ k ∧ method.direction k = 0) :
    method.finitelyTerminates := by
  rcases hZeroDirection with ⟨k, hk, hdir⟩
  exact ⟨k, hk, hDirectionZeroTerminated k hk hdir⟩

/-- If the recorded Step-2 stopping residual agrees stagewise with the source residual
`‖c_k‖ + ‖P̄_k g_k‖`, then the liminf branch of
`direction_zero_or_liminf_projectedGradientResidual_eq_zero_of_satisfiesAssumption1362`
gives finite termination for the recorded Algorithm 13.6.1 run. -/
theorem finitelyTerminates_of_liminf_projectedGradientResidual_eq_zero
    (method : Method)
    (hStoppingResidual :
      ∀ k : ℕ, 1 ≤ k →
        powellYuanStoppingResidual
            (method.constraintResidual k)
            (method.gradient k)
            (method.constraintJacobian k)
            (method.multiplier k) =
          method.projectedGradientResidualAt k)
    (hLiminf :
      Filter.liminf
          (fun k : ℕ ↦ method.projectedGradientResidualAt (k + 1))
          Filter.atTop = 0) :
    method.finitelyTerminates := sorry

/-- If the recorded Step-2 stopping residual agrees stagewise with the source residual
`‖c_k‖ + ‖P̄_k g_k‖`, and every stage with zero search direction already satisfies the recorded
Step-2 stopping test, then the source alternative from
`direction_zero_or_liminf_projectedGradientResidual_eq_zero_of_satisfiesAssumption1362`
gives finite termination for the recorded Algorithm 13.6.1 run. -/
theorem finitelyTerminates_of_satisfiesAssumption1362
    (method : Method)
    (h1362 : method.satisfiesAssumption1362)
    (hDirectionZeroTerminated :
      ∀ k : ℕ, 1 ≤ k → method.direction k = 0 → method.terminatedAt k)
    (hStoppingResidual :
      ∀ k : ℕ, 1 ≤ k →
        powellYuanStoppingResidual
            (method.constraintResidual k)
            (method.gradient k)
            (method.constraintJacobian k)
            (method.multiplier k) =
          method.projectedGradientResidualAt k) :
    method.finitelyTerminates := by
  rcases
      method.direction_zero_or_liminf_projectedGradientResidual_eq_zero_of_satisfiesAssumption1362
        h1362 with hZeroDirection | hLiminf
  · exact method.finitelyTerminates_of_exists_direction_zero
      hDirectionZeroTerminated hZeroDirection
  · exact method.finitelyTerminates_of_liminf_projectedGradientResidual_eq_zero
      hStoppingResidual hLiminf

end PowellYuanTrustRegionMethod

end
