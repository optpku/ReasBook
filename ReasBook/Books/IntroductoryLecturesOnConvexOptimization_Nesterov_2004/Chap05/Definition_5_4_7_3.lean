/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (positiveOrthant)
open scoped HessianLocalNorm RelativeDirection

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "X₂" => positiveOrthant 2

/- Definition 5.4.7.3 lies in the Chapter 5 positive-orthant barrier / local-Hessian-norm domain.

Sampled owner declarations:
* `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` from
  `Chap01/Definition_1_10_2`, the intrinsic strict positive-orthant owner;
* `standardLogarithmicBarrierAmbient` from `Definition_5_4_3_2`, the chapter ambient bridge for
  the positive-orthant logarithmic barrier;
* `hessianLocalNorm` from `Definition_5_1_1`, the chapter owner for local Hessian norms;
* `sigmaThree` from `Definition_5_4_6_8`, the source-facing squared-local-norm bridge.

Source/core/bridge triage:
* source-facing: `scaledDirectionSigma x h`, the textbook scalar `σ`;
* core/canonical: the squared local norm `sigmaThree (standardLogarithmicBarrierAmbient 2) x h`;
* bridge/view: the explicit coordinate formula `σ = (h₁ / x₁)^2 + (h₂ / x₂)^2`.

Primitive data:
* a strictly positive base point `x : positiveOrthant 2`;
* a direction `h : ℝ²`.

Derived API:
* the specialized squared local norm `scaledDirectionSigma x h`;
* the owner-level identity with `‖h‖[standardLogarithmicBarrierAmbient 2; x]^2`;
* the coordinate expansion theorem below.

The earlier version exposed a totalized coordinate formula on all of `ℝ²`, which lost the strict
positivity semantics of the source barrier geometry. The refined file keeps the strict-domain base
point as primitive data and reuses the chapter owner `sigmaThree`, leaving the coordinate formula
as a companion bridge theorem. -/

/-- Definition 5.4.7.3: for a strictly positive point `x ∈ ℝ_{++}²` and a direction `h ∈ ℝ²`,
the scalar `σ` is the squared local norm induced by the positive-orthant logarithmic barrier. -/
abbrev scaledDirectionSigma (x : X₂) (h : E₂) : ℝ :=
  sigmaThree (standardLogarithmicBarrierAmbient 2) x h

/-- Expanding `scaledDirectionSigma x h` gives the square of the canonical Hessian local norm of
the positive-orthant logarithmic barrier at `x`. -/
theorem scaledDirectionSigma_def (x : X₂) (h : E₂) :
    scaledDirectionSigma x h =
      ‖h‖[standardLogarithmicBarrierAmbient 2; x] ^ (2 : ℕ) :=
  rfl

/-- The scalar `scaledDirectionSigma x h` is the squared Euclidean norm of the relative direction
`δ_x(h)`, written in Lean as `δ[x](h)`. -/
theorem scaledDirectionSigma_eq_norm_relativeDirection (x : X₂) (h : E₂) :
    scaledDirectionSigma x h = ‖δ[x](h)‖ ^ (2 : ℕ) := by
  rw [scaledDirectionSigma_def, positiveOrthantLogarithmicBarrier_localNorm_eq_norm_relativeDirection]

/-- The scalar `scaledDirectionSigma x h` is the sum of squares of the two scaled direction
components. -/
theorem scaledDirectionSigma_eq (x : X₂) (h : E₂) :
    scaledDirectionSigma x h =
      (h 0 / (x : E₂) 0) ^ (2 : ℕ) + (h 1 / (x : E₂) 1) ^ (2 : ℕ) := by
  rw [scaledDirectionSigma_eq_norm_relativeDirection]
  simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq (δ[x](h))

end
