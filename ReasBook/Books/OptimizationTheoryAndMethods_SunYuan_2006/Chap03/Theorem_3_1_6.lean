/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_19
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_4

noncomputable section

open Filter

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Domain sampling:
-- * primary domain: local linear convergence of steepest descent with exact line search near a
--   nondegenerate limit point;
-- * source-facing surface for this theorem: the iterate sequence `x`, step sizes `α`, and the
--   Chapter 3 owner `IsSteepestDescentSequence f x α`, with the rate conclusion expressed by
--   the Chapter 3 owner `HasEventuallyLinearConvergenceTo`;
-- * core/canonical owners inspected: `HasEventuallyLinearConvergenceTo`,
--   `rLinearConvergenceTo`,
--   `HasHessianLowerBoundOn`,
--   `HasHessianUpperBoundOn`,
--   `exactLineSearch_atLeastLinearConvergenceTo_of_tendsto_isLocalMin_of_angleBound`,
--   `exactLineSearchSteepestDescent_accumulationPoint_stationary`,
--   `isStrictLocalMin_of_isStationaryPoint_of_iteratedFDeriv_pos`,
--   `steepestDescentDirection`, `steepestDescentStep`, `IsExactLineSearchStepOnNonnegativeRay`,
--   `IsStationaryPoint`, and `IsStrictLocalMin.isLocalMin`;
-- * bridge/view precedent: `IsSteepestDescentSequence.exactLineSearch` and
--   `IsSteepestDescentSequence.update` recover the Chapter 2 exact-line-search owner and the
--   Chapter 3 update equation without keeping them as parallel primitive hypotheses.
--
-- Triage:
-- * source-facing: this theorem is about a steepest-descent run converging at least linearly to
--   `xStar`;
-- * core/canonical: the direction/update/exact-line-search owners above together with the
--   Chapter 3 eventual-linear owner `HasEventuallyLinearConvergenceTo`;
-- * bridge/view removed here: the separate exact-line-search and update hypotheses, which are
--   already packaged by the Chapter 3 owner `IsSteepestDescentSequence`, and the redundant
--   stationary-point binder at `xStar`, which is derived from the convergent steepest-descent
--   run plus the local `C²` neighborhood hypothesis; the raw pointwise Hessian quadratic-form
--   binder on `Metric.ball xStar ε`, which is already owned in Chapter 1 by
--   `HasHessianLowerBoundOn` / `HasHessianUpperBoundOn`;
-- * stricter derived companions only: the global contraction owner
--   `HasLinearConvergenceTo` and the Chapter 1 rate owner `rLinearConvergenceTo`, which require
--   stronger data than the source-facing local hypotheses and exclude finite termination or
--   superlinear tails.
--
-- Primitive data are therefore just the steepest-descent iterate and step-size sequences together
-- with the Chapter 3 sequence owner `IsSteepestDescentSequence`, the local `C²` hypothesis, and
-- the Chapter 1 Hessian-bound owners on `Metric.ball xStar ε`. The search direction, exact line
-- search, and update clauses are derived through the sequence owner, the limit-point
-- stationarity and local-minimum bridge are internal consequences of the run plus those
-- canonical Hessian-bound owners, and the at-least-linear conclusion is expressed by the Chapter
-- 3 eventual-contraction owner `HasEventuallyLinearConvergenceTo`.

/-- Chapter03 Theorem 3.1.6: let `f : E → ℝ` on a real Hilbert space `E` be `C²` on a ball
about the limit point `xStar`, and suppose its Hessian quadratic form is bounded below by a
positive constant `m` and above by `M` on that ball, expressed by the Chapter 1 owners
`HasHessianLowerBoundOn` and `HasHessianUpperBoundOn`. If `x` and `α` form a Chapter 3
`IsSteepestDescentSequence` whose iterates tend to `xStar`, then `xStar` is forced to be
stationary by the convergent exact-line-search steepest-descent run, the lower Hessian bound
upgrades that stationary limit point to a local minimizer, and therefore `x` converges to
`xStar` at least linearly, expressed by the Chapter 3 eventual-contraction owner
`HasEventuallyLinearConvergenceTo` reused by the refined exact-line-search convergence theorem of
Chapter 2. The local Hessian control is only available near `xStar`, so the stronger global
contraction owner `HasLinearConvergenceTo` would require an additional run-in-ball hypothesis
from the initial iterate onward. This keeps the source-faithful “at least linear” owner rather
than the stricter Chapter 1 `R`-linear predicate, without keeping stationarity as redundant
public data. -/
theorem steepestDescent_atLeastLinear
    (f : E → ℝ)
    (x : ℕ → E)
    (α : ℕ → ℝ)
    (xStar : E)
    (ε m M : ℝ)
    (hε : 0 < ε)
    (hm : 0 < m)
    (hC2 : ContDiffOn ℝ 2 f (Metric.ball xStar ε))
    (hLower : HasHessianLowerBoundOn (Metric.ball xStar ε) f m)
    (hUpper : HasHessianUpperBoundOn (Metric.ball xStar ε) f M)
    (hSeq : IsSteepestDescentSequence f x α)
    (hTendsto : Tendsto x atTop (nhds xStar)) :
    HasEventuallyLinearConvergenceTo x xStar := sorry

end
