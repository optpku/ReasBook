/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_4

open scoped Gradient MatrixOrder StrongConvexSmooth

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Primary domain: smooth strongly convex objectives on Euclidean space.

Sampled owner-style declarations before refining this file:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`
* `IsStrongConvexSmoothObjective.iff_contDiff_and_gradient_strong_mono` in `Definition_2_17`
* `quadraticObjective` in `Definition_1_9_1`
* `quadraticObjective_mem_S11` in `Proposition_2_4`

Best owner abstractions:
* `IsStrongConvexSmoothObjective μ L f` for the objective class
* `quadraticObjective` for the canonical Euclidean quadratic model

Primitive data:
* `0 < μ`, `ContDiff ℝ 1 f`, `StrongConvexOn Set.univ μ f`, and the Euclidean
  gradient-Lipschitz bound
* for the model example, the owner quadratic `quadraticObjective 0 0 (μ • 1)`

Derived API:
* the source-facing membership bridge `mem_S11_iff`
* the Euclidean characterization of `f ∈ 𝓢[μ, L]¹¹` via whole-space strong
  gradient monotonicity
-/

/- Definition 2.16 is the source-facing Euclidean recall of the smooth strongly convex class
`𝓢^{1,1}_{μ,L}(ℝⁿ)`. The core owner remains the Hilbert-space predicate from `Definition_2_17`,
but this file centers its public surface on the textbook class notation `f ∈ 𝓢[μ, L]¹¹`; the
owner predicate is accessed only through the canonical bridge `mem_S11_iff`. -/
variable (μ L : ℝ) (f : E → ℝ) in
#check f ∈ 𝓢[μ, L]¹¹

/- The whole-space notation `𝓢[μ, L]¹¹` is the source-facing set view of the chapter owner
predicate `IsStrongConvexSmoothObjective μ L`. -/
recall mem_S11_iff

/-- Definition 2.16: the Euclidean source-facing class `𝓢[μ, L]¹¹` is equivalently the textbook
combination of `C¹` regularity, positive strong convexity modulus, and the whole-space strong
gradient-monotonicity and gradient-Lipschitz estimates. -/
theorem mem_S11_iff_contDiff_and_gradient_strong_mono {μ L : ℝ} {f : E → ℝ} :
    f ∈ 𝓢[μ, L]¹¹ ↔
      0 < μ ∧
        ContDiff ℝ 1 f ∧
        (∀ x y : E,
          μ * ‖x - y‖ ^ (2 : ℕ) ≤ inner ℝ (∇ f x - ∇ f y) (x - y)) ∧
        ∀ x y : E, ‖∇ f x - ∇ f y‖ ≤ L * ‖x - y‖ := by
  constructor
  · intro hf
    exact
      (IsStrongConvexSmoothObjective.iff_contDiff_and_gradient_strong_mono).mp
        (mem_S11_iff.mp hf)
  · intro hf
    exact
      mem_S11_iff.mpr
        ((IsStrongConvexSmoothObjective.iff_contDiff_and_gradient_strong_mono).mpr hf)

/- The centered quadratic textbook model is the specialization of the canonical Proposition 2.4
owner theorem, so this file keeps only the direct recall surface rather than a duplicate theorem
with the same interface. -/
recall quadraticObjective_mem_S11
