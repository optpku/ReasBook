/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_4_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_6
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_7
import Mathlib.Order.Filter.Basic

noncomputable section

open Filter
open scoped Matrix.Norms.L2Operator

section Chapter05Theorem548

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling for this refine pass:
-- * primary domain: local scaled quasi-Newton convergence on the Euclidean matrix model of
--   `ℝ^n`;
-- * sampled owner declarations in the minimal closure:
--   `quasiNewtonHessianSecantErrorRatio` from `Theorem_5_4_6`,
--   `ScaledQuasiNewtonSetup (gradient f) D`,
--   `ScaledQuasiNewtonSetup.matrix`,
--   `scaledQuasiNewton_stepsizes_tendsto_one_of_secantErrorRatio_tendsto_zero`,
--   and `scaledQuasiNewton_qsuperlinear_of_secantErrorRatio_tendsto_zero`
--   from `Theorem_5_4_7`,
--   together with `HasQuasiNewtonStrongLocalMinimizerAssumptions` from `Assumption_5_4_2`;
-- * layer triage:
--   source-facing theorem item: the Hessian-side matrix specialization of the local secant-error
--   hypothesis from Theorem 5.4.8;
--   core/canonical owner: `ScaledQuasiNewtonSetup (gradient f) D`;
--   bridge/view reused here: `A.matrix` and `quasiNewtonHessianSecantErrorRatio`;
-- * primitive data: `f`, the local-minimizer assumptions `h`, the scaled quasi-Newton run owner
--   `A`, convergence of `A.x`, and the Hessian-side secant-error limit;
-- * derived API reused here: the step-size and `Q`-superlinear conclusions already owned by
--   `Theorem_5_4_7`.

/-- Chapter05 Theorem 5.4.8 (1): on the canonical scaled quasi-Newton owner
`A : ScaledQuasiNewtonSetup (gradient f) D`, the Hessian-side source ratio `(5.4.25)` is only the
Euclidean matrix-model view of the secant-error owner from `Theorem_5_4_7`. The step-size
conclusion is therefore a thin bridge to
`scaledQuasiNewton_stepsizes_tendsto_one_of_secantErrorRatio_tendsto_zero`, with no additional
Wolfe-Powell or noncollision hypotheses in the public statement. -/
theorem scaledQuasiNewton_stepsizes_tendsto_one_of_hessianSecantError
    {D : Set Point}
    (f : Point → ℝ)
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f)
    (A : ScaledQuasiNewtonSetup (gradient f) D)
    (hx : Tendsto A.x atTop (nhds h.xStar))
    (h_secantError :
      Tendsto (quasiNewtonHessianSecantErrorRatio f h.xStar A.matrix A.x) atTop (nhds 0)) :
    Tendsto A.α atTop (nhds 1) := by
  exact scaledQuasiNewton_stepsizes_tendsto_one_of_secantErrorRatio_tendsto_zero f h A hx <|
    by
      simpa [quasiNewtonHessianSecantErrorRatio_eq_secantErrorRatio]
        using h_secantError

/- Chapter05 Theorem 5.4.8 (2): the `Q`-superlinear conclusion is already the canonical
Chapter 5 scaled quasi-Newton theorem
`scaledQuasiNewton_qsuperlinear_of_secantErrorRatio_tendsto_zero`,
specialized through the owner-level source-facing Hessian-side matrix view of `A.B`. This clause
therefore stays at the recall layer and introduces no duplicate local theorem surface. -/
#check
  fun {D : Set Point}
      (f : Point → ℝ)
      (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f)
      (A : ScaledQuasiNewtonSetup (gradient f) D)
      (hx : Tendsto A.x atTop (nhds h.xStar))
      (h_secantError :
        Tendsto (quasiNewtonHessianSecantErrorRatio f h.xStar A.matrix A.x) atTop (nhds 0)) ↦
    (scaledQuasiNewton_qsuperlinear_of_secantErrorRatio_tendsto_zero f h A hx <| by
      simpa [quasiNewtonHessianSecantErrorRatio_eq_secantErrorRatio] using h_secantError :
        HasQSuperlinearConvergenceTo A.x h.xStar)

end Chapter05Theorem548
