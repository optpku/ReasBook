/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_4_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_4
import Mathlib.Order.Filter.Basic

noncomputable section

open Filter

section Chapter05Theorem547

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-
Domain sampling for this refine pass:
* primary domain: local scaled quasi-Newton convergence for smooth objectives on `ℝ^n`;
* sampled owner declarations in this domain:
  `HasQuasiNewtonStrongLocalMinimizerAssumptions.gradient_eq_zero`,
  `HasQuasiNewtonStrongLocalMinimizerAssumptions.toHasScaledQuasiNewtonLocalAssumptions`,
  `ScaledQuasiNewtonSetup`,
  `quasiNewton_superlinear_of_secantErrorRatio_tendsto_zero`,
  and `quasiNewton_zero_iff_stepsizes_tendsto_one`
  from `Theorem_5_4_4`;
* source/core/bridge triage:
  this file stays at the `source-facing` theorem layer;
  `HasQuasiNewtonStrongLocalMinimizerAssumptions` is the owner abstraction for the Chapter 5
  hypotheses and now owns its derived zero-gradient and scaled-local-assumption bridges;
  `ScaledQuasiNewtonSetup (gradient f) D` is the run owner for clauses (1) and (3);
  the Euclidean Hessian-side ratio from `Theorem_5_4_6` remains only a bridge/view of the
  canonical secant-error owner `quasiNewtonSecantErrorRatio`.
* primitive data retained here: `f`, the Assumption 5.4.2 owner `h`, and the scaled
  quasi-Newton run owner `A`.
* derived API consumed here: the owner-level zero-gradient theorem, the owner-level bridge to
  `HasScaledQuasiNewtonLocalAssumptions`, and the stepsize and `Q`-superlinear conclusions.
-/

/-- Chapter05 Theorem 5.4.7 (1): let `f : ℝ^n → ℝ` satisfy
`HasQuasiNewtonStrongLocalMinimizerAssumptions D f`, and let
`A : ScaledQuasiNewtonSetup (gradient f) D` be the scaled quasi-Newton run owner.
If `A.x` converges to `h.xStar` and the canonical secant-error ratio for `gradient f`
tends to `0`, then the step sizes satisfy `A.α k → 1`. The source Hessian-side ratio from
`Theorem_5_4_6` is the Euclidean matrix-model view of this owner-level hypothesis. -/
theorem scaledQuasiNewton_stepsizes_tendsto_one_of_secantErrorRatio_tendsto_zero
    {D : Set Point}
    (f : Point → ℝ)
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f)
    (A : ScaledQuasiNewtonSetup (gradient f) D)
    (hx : Tendsto A.x atTop (nhds h.xStar))
    (h_secantError :
      Tendsto (quasiNewtonSecantErrorRatio (gradient f) h.xStar A.B A.x) atTop (nhds 0)) :
    Tendsto A.α atTop (nhds 1) := by
  exact (quasiNewton_zero_iff_stepsizes_tendsto_one
    (gradient f) h.toHasScaledQuasiNewtonLocalAssumptions A hx h_secantError).mp
      h.gradient_eq_zero

/- Chapter05 Theorem 5.4.7 (2): the distinguished point in
`HasQuasiNewtonStrongLocalMinimizerAssumptions D f` already satisfies the owner-level stationary
point consequence `h.gradient_eq_zero`, so this clause remains at the recall layer. -/
#check
  fun {D : Set Point}
      (f : Point → ℝ)
      (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) ↦
    (h.gradient_eq_zero : gradient f h.xStar = 0)

/-- Chapter05 Theorem 5.4.7 (3): for the scaled quasi-Newton run owner
`A : ScaledQuasiNewtonSetup (gradient f) D`, if `A.x` converges to `h.xStar` and the canonical
secant-error ratio for `gradient f` tends to `0`, then `A.x` converges to `h.xStar`
`Q`-superlinearly. This keeps the conclusion on the scaled quasi-Newton owner from
`Theorem_5_4_4`; the Euclidean Hessian-side ratio remains a companion bridge/view rather than
the main public owner. -/
theorem scaledQuasiNewton_qsuperlinear_of_secantErrorRatio_tendsto_zero
    {D : Set Point}
    (f : Point → ℝ)
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f)
    (A : ScaledQuasiNewtonSetup (gradient f) D)
    (hx : Tendsto A.x atTop (nhds h.xStar))
    (h_secantError :
      Tendsto (quasiNewtonSecantErrorRatio (gradient f) h.xStar A.B A.x) atTop (nhds 0)) :
    HasQSuperlinearConvergenceTo A.x h.xStar := by
  exact quasiNewton_superlinear_of_secantErrorRatio_tendsto_zero
    (gradient f) h.toHasScaledQuasiNewtonLocalAssumptions A hx h_secantError

end Chapter05Theorem547
