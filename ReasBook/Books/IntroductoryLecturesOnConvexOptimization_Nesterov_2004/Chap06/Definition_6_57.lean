/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

/- Definition 6.57 [Estimating functional sequence]: the Chapter 6 estimating sequence `φ_t` is
the recursively defined family with `φ_0(x) = a_0 * \tilde f(x)` and
`φ_{t+1}(x) = φ_t(x) + a_{t+1} * (f(x_t) + ∇f(x_t)(x - x_t) + Ψ(x))`. This is exactly the
chapter owner `ConditionalGradientContraction.estimatingFunctionalSequence`, so the item is
formalized as a direct recall of that canonical recursive definition. -/
recall ConditionalGradientContraction.estimatingFunctionalSequence
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → ℝ) (tildeF f : E → ℝ) (gradF : E → StrongDual ℝ E) (Ψ : E → ℝ)
    (xSeq : ℕ → E) :
    ℕ → E → ℝ

end

end
