/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.MetricSpace.Lipschitz

import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_19
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Algorithm_4_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Theorem_4_3_4

noncomputable section

open Filter

section DaiYuanCoefficient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Dai-Yuan coefficient
`β_k = ‖g_(k + 1)‖² / ⟪d_k, g_(k + 1) - g_k⟫_ℝ`. -/
def daiYuanBeta (gPrev gNext dPrev : E) : ℝ :=
  ‖gNext‖ ^ (2 : ℕ) / inner ℝ dPrev (gNext - gPrev)

end DaiYuanCoefficient

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ}

-- Domain sampling pass:
-- * primary domain: nonlinear conjugate-gradient runs on a real complete inner-product space
--   with Wolfe-Powell inexact line
--   search and Dai-Yuan direction updates
-- * inspected owner declarations in this domain:
--   - `ConjugateGradientRun E` from `Algorithm_4_2_extra_1` for the primitive nonlinear
--     conjugate-gradient run data and the `HasGradientAt`-backed gradient interface
--   - `ConjugateGradientRun.gradient_eq` from `Algorithm_4_2_extra_1` for the canonical bridge
--     from recorded gradients `method.g k` to the owner `gradient f (method.x k)`
--   - `ConjugateGradientRun.HasStationaryContinuation` from `Algorithm_4_2_extra_1` for the
--     canonical post-termination stationarity bridge on the infinite-sequence run owner
--   - `ConjugateGradientRun.WolfePowell` and `ConjugateGradientRun.StrongWolfePowell` from
--     `Theorem_4_3_4` as the run-level Wolfe bridges layered on the existing run owner
--   - `IsDescentDirectionAt` from `Chapter01.Definition_1_4_3` as the canonical owner of the
--     descent-direction notion used by the first theorem
--   - `WolfePowellParameters` from Chapter 2 as the canonical owner of the admissible
--     Wolfe-Powell parameter inequalities
-- * best owner abstraction here: the chapter owner `ConjugateGradientRun`, with a Dai-Yuan
--   bridge carrying only the Wolfe-Powell and Dai-Yuan-specific step laws
-- * layer targeted by the rewrite: `source-facing` theorem surfaces over the `bridge/view`
--   owner `ConjugateGradientRun.DaiYuan`
-- Primitive data vs derived API:
-- * primitive data: the initial point, iterate sequence, explicit gradient sequence, search
--   directions, step sizes, and `HasGradientAt` witnesses already owned by
--   `ConjugateGradientRun`
-- * derived API here: the canonical weak-Wolfe acceptance predicate on the accepted line-search
--   profile together with the canonical post-termination stationarity bridge, the nonvanishing
--   Dai-Yuan denominator, and the Dai-Yuan direction update

namespace ConjugateGradientRun

/-- A nonlinear conjugate-gradient run is a Dai-Yuan run with Wolfe-Powell line search when it
starts in the steepest-descent direction, each nonstationary step satisfies the reusable
run-level Wolfe-Powell bridge from `Theorem_4_3_4`, the Dai-Yuan denominator is nonzero whenever
the current and next gradients are nonzero, and the next direction is given by the Dai-Yuan
update formula. This is a `bridge/view` on the chapter owner `ConjugateGradientRun`, not a
second run owner. -/
structure DaiYuan (f : E → ℝ) (method : ConjugateGradientRun E f)
    extends WolfePowell f method where
  direction_zero : method.d 0 = -method.g 0
  betaDenominatorNonzero (k : ℕ) (hk : method.g k ≠ 0) (hkNext : method.g (k + 1) ≠ 0) :
      inner ℝ (method.d k) (method.g (k + 1) - method.g k) ≠ 0
  direction_update (k : ℕ) (hk : method.g k ≠ 0) (hkNext : method.g (k + 1) ≠ 0) :
      method.d (k + 1) =
        -method.g (k + 1) + daiYuanBeta (method.g k) (method.g (k + 1)) (method.d k) • method.d k

end ConjugateGradientRun

namespace ConjugateGradientRun.DaiYuan

variable {method : ConjugateGradientRun E f}

local notation "LevelSet" => lowerLevelSetOn Set.univ f method.x0

/-- Chapter04 Theorem 4.3.6 (1): in a Dai-Yuan conjugate-gradient run with Wolfe-Powell steps,
every nonstationary search direction is a descent direction at the current iterate, expressed
through the canonical owner `IsDescentDirectionAt f (method.x k) (method.d k)`. -/
theorem descentDirection
    (hDaiYuan : DaiYuan f method) (k : ℕ) (hk : method.g k ≠ 0) :
    IsDescentDirectionAt f (method.x k) (method.d k) := sorry

/-- Chapter04 Theorem 4.3.6 (2): under `C¹` regularity on the canonical lower level set
`LevelSet`, the lower-level-set lower-bound and gradient-Lipschitz hypotheses there, together
with the Dai-Yuan Wolfe-Powell and post-termination stationary-continuation bridges recorded
here, allowing finite termination at a stationary point, the source conclusion holds in its
direct filter form on the canonical gradient along the iterate sequence:
`liminf (fun k : ℕ ↦ ‖gradient f (method.x k)‖) atTop = 0`. -/
theorem gradientNorm_liminf_zero
    (hDaiYuan : DaiYuan f method)
    (hStationary : method.HasStationaryContinuation)
    (hC1 : ContDiffOn ℝ 1 f LevelSet)
    (hBddBelow : BddBelow (f '' LevelSet))
    (hGradLipschitz : ∃ L : NNReal, LipschitzOnWith L (gradient f) LevelSet) :
    liminf (fun k : ℕ ↦ ‖gradient f (method.x k)‖) atTop = 0 := sorry

end ConjugateGradientRun.DaiYuan

end
