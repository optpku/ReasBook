/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_47
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

open scoped StronglyConvexProblemClass

/-
Definition 3.48 is a source-facing recall in the chapter's first-order black-box complexity
domain for strongly convex unconstrained objectives.

Primary domain:
* the strongly convex local-ball problem class `𝒫_s(x₀, μ, M)`

Sampled owner-style declarations:
* `𝒫_s(x₀, μ, M)` / `IsInStronglyConvexProblemClass` in `Theorem_3_47`
* `𝒮^0_μ(Q)` / `mem_S0On_iff` in `Definition_3_47`
* `StrongConvexOnClass`
* `IsMinOn`
* `LipschitzOnWith`
* `IsInLipschitzConvexProblemClass` in `Theorem_3_2_1`

Best owner abstraction:
* source-facing: `𝒫_s(x0, μ, M) f xStar`
* core/canonical:
  `f ∈ 𝒮^0_((μ : ℝ))(Metric.closedBall xStar ‖x0 - xStar‖)`,
  `IsMinOn f Set.univ xStar`, and
  `LipschitzOnWith M f (Metric.closedBall xStar ‖x0 - xStar‖)`
* bridge/view: the stronger whole-space class
  `IsInLipschitzConvexProblemClass x0 ‖x0 - xStar‖₊ M f xStar`, available separately when an
  additional global convexity hypothesis is supplied

Primitive data:
* the objective `f : V → ℝ`
* the chosen minimizer `xStar : V`

Derived API:
* the positivity, strong-convexity, minimizer, and Lipschitz accessors already owned by
  `𝒫_s(x0, μ, M)`
* the stronger whole-space bridge data, kept outside this recall file

Source/core/bridge triage:
* source-facing: `𝒫_s(x0, μ, M) f xStar`
* core/canonical: the component owners `𝒮^0_((μ : ℝ))(Metric.closedBall xStar ‖x0 - xStar‖)`,
  `IsMinOn`, and `LipschitzOnWith`
* bridge/view: the stronger whole-space class `IsInLipschitzConvexProblemClass`

This file therefore recalls the earlier chapter owner through its scoped source notation rather
than recentering the longer raw backing declaration name.
-/

variable (x0 : V) (μ M : NNReal)

/- Definition 3.48 recalls the source-facing strongly convex problem class `𝒫_s(x₀, μ, M)`. -/
#check (𝒫_s(x0, μ, M) : (V → ℝ) → V → Prop)

end
