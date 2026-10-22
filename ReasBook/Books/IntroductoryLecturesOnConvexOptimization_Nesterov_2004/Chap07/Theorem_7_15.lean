/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Theorem_7_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_58

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open scoped Gradient HessianDualLocalNorm

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace DualBarrierSubgradientMethod

variable {P : Set E} {f : E → ℝ}

/-- Theorem 7.15: under the Chapter 7 parameter choice `(7.3.19)`, if `method.F` is a genuine
`ν`-self-concordant barrier on `P` in the Chapter 5 sense, then the normalized maximal gap of a
`DualBarrierSubgradientMethod` is bounded by the explicit closed-form rate. -/
theorem maximalGap_le_explicit_rate
    (method : DualBarrierSubgradientMethod P f)
    (M ν : NNReal) [IsSelfConcordantBarrierForWith P ν method.F]
    [HasPositiveDefiniteHessianOn P method.F]
    (hν : 0 < (ν : ℝ))
    (hdual :
      ∀ x : P,
        HessianDualLocalNorm.ofPosDefMem method.F x.2 (method.dualSubgradient x) ≤ (M : ℝ))
    (hstep : ∀ i : ℕ, (method.stepSize i : ℝ) = barrierSubgradientLambda i)
    (hbeta : ∀ i : ℕ, (method.beta i : ℝ) = barrierSubgradientBeta M ⟨(ν : ℝ), hν⟩ i)
    (k : ℕ) :
    method.maximalGap k /
      barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k ≤
      ((2 * (M : ℝ) *
          (Real.sqrt ((ν : ℝ) / ((k : ℝ) + 1)) + (ν : ℝ) / ((k : ℝ) + 1)) *
            (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1)))) : ℝ)) :=
  sorry

end DualBarrierSubgradientMethod
