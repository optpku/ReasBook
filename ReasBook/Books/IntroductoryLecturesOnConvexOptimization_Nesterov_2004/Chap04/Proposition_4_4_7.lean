/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

/- Proposition 4.4.7 lies in the modified Gauss--Newton trajectory / merit-function domain.

Sampled owner declarations:
* `Antitone` and `antitone_nat_of_succ_le` in mathlib, the canonical owner/bridge pair for
  nonincreasing real sequences on `ℕ`;
* `ModifiedGaussNewtonMethod.step_value_le_modelValue` in `Algorithm_4_4_1`, the owner-side
  accepted-step decrease inequality;
* `ModifiedGaussNewtonMethod.step_modelValue_le_merit` in `Algorithm_4_4_1`, the owner-side
  comparison between the local model and the current merit value.

Best owner abstraction:
* source-facing: the one-step monotonicity of the merit values along a modified Gauss--Newton
  method;
* core/canonical: `Antitone (fun k ↦ f (method k))` on the run owner
  `ModifiedGaussNewtonMethod`;
* bridge/view: the successor-step inequality `f (method (k + 1)) ≤ f (method k)`.

Primitive data:
* the method `method`.

Derived API:
* the stepwise merit decrease `f(x_{k+1}) ≤ f(x_k)`.
* the antitone merit-value sequence `Antitone (fun k ↦ f (method k))`.

This file therefore keeps Proposition 4.4.7 as an owner theorem of
`ModifiedGaussNewtonMethod`, rather than as a separate globally prefixed wrapper around the same
owner-side inequalities, and exposes the canonical antitone companion theorem for downstream use.
-/

namespace ModifiedGaussNewtonMethod

section

variable {problem : SmoothMap}
variable {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
variable {L0 L : ℝ} {x0 : E₁}

local notation "f" => meritFunctionReformulation problem φ

-- Proof sketch: compose the owner-side acceptance inequality
-- `method.step_value_le_modelValue k` with the owner-side comparison
-- `method.step_modelValue_le_merit k`.
/-- Proposition 4.4.7: the modified Gauss--Newton iterates produced by Algorithm 4.4.1 have
nonincreasing merit-function values, so
`f(x_{k+1}) ≤ f(x_k)` for every iteration index `k`. -/
theorem meritFunction_succ_le
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) (k : ℕ) :
    f (method (k + 1)) ≤ f (method k) :=
  le_trans (method.step_value_le_modelValue k) (method.step_modelValue_le_merit k)

/-- The merit-function values along a modified Gauss--Newton method form an antitone sequence. -/
theorem meritFunction_antitone
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) :
    Antitone (fun k ↦ f (method k)) :=
  antitone_nat_of_succ_le fun k ↦ method.meritFunction_succ_le k

end

end ModifiedGaussNewtonMethod

end
