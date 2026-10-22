/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Order.Filter.AtTopBot.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Algorithm_11_3_1

noncomputable section

open Filter
open scoped Matrix.Norms.Frobenius

section Chapter11Theorem1133

variable {basicDim nonbasicDim : ℕ}

local notation "AcceptedStepRun" =>
  @_root_.GeneralizedReducedGradientAcceptedStepRun basicDim nonbasicDim

namespace GeneralizedReducedGradientAcceptedStepRun

/-- Chapter11 Theorem 11.3.3: assume that `f(x)` and `c(x)` are twice continuously
differentiable for a generalized reduced-gradient accepted-step run
`run : GeneralizedReducedGradientAcceptedStepRun`, that the inherited Step 2 inverse blocks
`A_B(x_k)⁻¹` are uniformly bounded above on active stages, and that the Step 3 initial
steplengths `α_k⁽⁰⁾` satisfy `(11.3.6)` and `(11.3.7)`. This canonical accepted-step owner keeps
the Step 7 decrease and iterate-update data needed to connect the Step 3 steplength hypotheses to
the actual evolution of `x_k`. If `run.ε = 0` and the algorithm does not terminate, then either
the reduced-gradient norms satisfy `‖g̃_k‖ → 0`, or the objective values satisfy
`f(x_k) → -∞`. -/
theorem reducedGradientNorm_tendsto_zero_or_objective_tendsto_atBot_of_step3Hypotheses
    (run : AcceptedStepRun)
    (hC2f : ContDiff ℝ 2 run.objective)
    (hC2c : ContDiff ℝ 2 run.constraint)
    (hBoundedInverse :
      run.toGeneralizedReducedGradientRun.uniformlyBoundedBasicJacobianInverse)
    (h1136 :
      run.toGeneralizedReducedGradientRun.initialStepSizeLowerBoundByReducedGradient)
    (h1137 :
      run.toGeneralizedReducedGradientRun.initialStepSizeOverReducedGradientNormPartialSumsDiverge)
    (hε : run.ε = 0)
    (hNonterminating : ∀ k, 1 ≤ k → run.active k) :
    Tendsto (fun k : ℕ ↦ ‖run.reducedGradient k‖) atTop (nhds (0 : ℝ)) ∨
      Tendsto (fun k : ℕ ↦ run.objective (run.iterate k)) atTop atBot := sorry

end GeneralizedReducedGradientAcceptedStepRun

end Chapter11Theorem1133
