/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_6_4

open Filter Asymptotics

section InexactNewtonMethod

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Domain sampling:
-- * `Theorem_3_6_2`: `IsRegularZero`
-- * `Algorithm_3_6_extra_2`: `IsInexactNewtonSequence`
-- * `Theorem_3_6_6`: `HasInexactNewtonForcingBound`
-- * `Theorem_3_6_4`: `inexactNewton_residual_isLittleO_iff_qSuperlinear`
-- * `Mathlib.Analysis.Asymptotics.Lemmas`: `=o[atTop]`
--
-- Source/core/bridge triage:
-- * source-facing: the forcing-to-superlinear corollary
-- * core/canonical: `IsRegularZero`, `IsInexactNewtonSequence`,
--   `HasInexactNewtonForcingBound`, and the asymptotic `=o` owner
-- * bridge/view: reuse of the upstream Chapter 3.6 owners on the corollary surface

/-- If the forcing sequence `ηSeq` of an inexact Newton sequence tends to `0`, then the
residuals satisfy the little-`o` condition from Theorem 3.6.4. -/
theorem IsInexactNewtonSequence.residual_isLittleO_of_forcing_tendsto_zero
    {F : E → E} {x s r : ℕ → E} {ηSeq : ℕ → ℝ} {η : ℝ}
    (h_inexact : IsInexactNewtonSequence F x s r ηSeq)
    (hη_bound : HasInexactNewtonForcingBound ηSeq η)
    (hηSeq_tendsto_zero : Tendsto ηSeq atTop (nhds 0)) :
    ((fun k ↦ ‖r k‖) =o[atTop] fun k ↦ ‖F (x k)‖) := by
  have hηSeq_isLittleO :
      (fun k ↦ ηSeq k) =o[atTop] fun _ ↦ (1 : ℝ) := by
    rw [isLittleO_one_iff ℝ]
    simpa using hηSeq_tendsto_zero
  have h_forcing_mul_isLittleO :
      (fun k ↦ ηSeq k * ‖F (x k)‖) =o[atTop] fun k ↦ ‖F (x k)‖ := by
    simpa using hηSeq_isLittleO.mul_isBigO (isBigO_refl (fun k ↦ ‖F (x k)‖) atTop)
  exact
    (h_inexact.residual_isBigO hη_bound.nonneg).trans_isLittleO h_forcing_mul_isLittleO

/-- Chapter03 Corollary 3.6.5: under the assumptions of Theorem 3.6.4 for an inexact Newton
sequence `x` converging to `xStar`, if the forcing sequence `ηSeq` tends to `0`, then `x`
converges to `xStar` `Q`-superlinearly. -/
theorem inexactNewton_qSuperlinear_of_forcing_tendsto_zero
    (F : E → E) (xStar : E) (η : ℝ)
    (h_regular : IsRegularZero F xStar)
    (hη_lt_one : η < 1)
    (x s r : ℕ → E) (ηSeq : ℕ → ℝ)
    (h_inexact : IsInexactNewtonSequence F x s r ηSeq)
    (hη_bound : HasInexactNewtonForcingBound ηSeq η)
    (hx : Tendsto x atTop (nhds xStar))
    (hηSeq_tendsto_zero : Tendsto ηSeq atTop (nhds 0)) :
    HasSuperlinearConvergenceTo x xStar := by
  exact
    (inexactNewton_residual_isLittleO_iff_qSuperlinear
      F xStar η h_regular hη_lt_one x s r ηSeq h_inexact hη_bound hx).mp <|
      h_inexact.residual_isLittleO_of_forcing_tendsto_zero hη_bound hηSeq_tendsto_zero

end InexactNewtonMethod
