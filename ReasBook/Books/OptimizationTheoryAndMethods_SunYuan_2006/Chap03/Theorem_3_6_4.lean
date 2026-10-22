/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_6_6
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Order.Filter.Basic

open Filter

section InexactNewtonMethod

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Domain sampling:
-- * `Theorem_3_6_2`: `IsRegularZero`
-- * `Algorithm_3_6_extra_2`: `IsInexactNewtonSequence`
-- * `Theorem_3_6_6`: `HasInexactNewtonForcingBound`
-- * `Theorem_3_4_4`: `HasSuperlinearConvergenceTo`
-- * `Mathlib.Analysis.Asymptotics.Lemmas`: `=o[atTop]`
--
-- Source/core/bridge triage:
-- * source-facing: the theorem's residual-vs-superlinear equivalence
-- * core/canonical: `IsRegularZero`, `IsInexactNewtonSequence`,
--   `HasInexactNewtonForcingBound`, `HasSuperlinearConvergenceTo`, and the
--   asymptotic `=o` owner
-- * bridge/view: under the ambient convergence hypothesis `hx`, the source-side
--   `Q`-superlinear rate is expressed by the canonical owner
--   `HasSuperlinearConvergenceTo x xStar`

/-- Chapter03 Theorem 3.6.4: for an inexact Newton sequence `x` at a regular zero `xStar`,
if the forcing sequence is bounded by `η < 1` and `x ⟶ xStar`, then the residual condition
`‖r k‖ = o(‖F (x k)‖)` is equivalent to `Q`-superlinear convergence of `x` to `xStar`,
expressed by the canonical owners `HasInexactNewtonForcingBound ηSeq η` and
`HasSuperlinearConvergenceTo x xStar`. -/
theorem inexactNewton_residual_isLittleO_iff_qSuperlinear
    (F : E → E) (xStar : E) (η : ℝ)
    (h_regular : IsRegularZero F xStar)
    (hη_lt_one : η < 1)
    (x s r : ℕ → E) (ηSeq : ℕ → ℝ)
    (h_inexact : IsInexactNewtonSequence F x s r ηSeq)
    (hη_bound : HasInexactNewtonForcingBound ηSeq η)
    (hx : Tendsto x atTop (nhds xStar)) :
    ((fun k ↦ ‖r k‖) =o[atTop] fun k ↦ ‖F (x k)‖) ↔
      HasSuperlinearConvergenceTo x xStar := sorry

end InexactNewtonMethod
