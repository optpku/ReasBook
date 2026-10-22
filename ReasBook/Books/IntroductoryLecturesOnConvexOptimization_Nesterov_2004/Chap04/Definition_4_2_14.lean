/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 4.2.14 lies in the chapter's cubic-regularized estimating-sequence domain.

Sampled owner-style declarations:
* `IsEstimatingSequence` in `Chap02/Definition_2_21`, the chapter's generic upper-model owner for
  estimating sequences;
* `AcceleratedCubicNewtonMethod` in `Algorithm_4_2_2`, which packages a sequence of estimating
  functions together with minimizing points;
* `OptimalCubicNewtonMethod` in `Algorithm_4_3_1`, the same owner pattern for the optimal cubic
  Newton scheme;
* `sampledAffineMinorant` in `Chap03/Proposition_3_26`, which uses the canonical affine-map owner
  `E →ᵃ[ℝ] ℝ` for affine lower models with constant terms.

Best owner abstraction:
* source-facing: `CubicNewtonEstimatingSequence f x0 L3 C`, because Definition 4.2.14 adds the
  cubic-specific recursion and minimizing data, not just a bare Chapter 2 estimating-sequence
  inequality;
* core/canonical for the noncubic part of `ψ_k`: the affine-map owner `E →ᵃ[ℝ] ℝ`, since the
  chapter's initialization and affine-gradient updates include constant terms;
* bridge/view: `cubicNewtonEstimatingFunction affinePart C x0`, whose pointwise expansion
  recovers the textbook formula.

Primitive data:
* the affine parts `ℓ_k`;
* the points `x_k`;
* the scales `A_k` and increments `a_k`;
* the recursion `A_{k+1} = A_k + a_k`;
* the minimizing property and the two source inequalities.

Derived API:
* the estimating-function family `ψ_k` itself, obtained canonically from `affinePart`, `C`, and
  `x0`;
* pointwise expansion of `ψ_k`;
* convenient theorems phrased with the coercion `sequence k x`.

Refinement outcome:
* keep the source-facing structure;
* widen the noncubic owner from linear maps to the canonical affine-map owner `E →ᵃ[ℝ] ℝ`;
* use `cubicNewtonEstimatingFunction` and the coercion as the public surface.
-/

/-- The cubic estimating functions built from a sequence of affine parts `ℓ_k`, a base point `x0`,
and a cubic regularization parameter `C`. This is the stagewise cubic regularization owner from
Definition 4.2.16 applied to the affine parts `ℓ_k`, with parameter `C / 2` so that the penalty
term is `(C / 6) ‖x - x0‖^3`. -/
abbrev cubicNewtonEstimatingFunction
    (affinePart : ℕ → E →ᵃ[ℝ] ℝ) (C : ℝ) (x0 : E) :
    ℕ → E → ℝ :=
  fun k ↦ cubicallyRegularizedObjective (affinePart k) (C / 2) x0

/-- Evaluating the cubic-Newton estimating function at stage `k` recovers
`ℓ_k(x) + (C / 6) ‖x - x0‖^3`. -/
@[simp] theorem cubicNewtonEstimatingFunction_apply
    (affinePart : ℕ → E →ᵃ[ℝ] ℝ) (C : ℝ) (x0 : E) (k : ℕ) (x : E) :
    cubicNewtonEstimatingFunction affinePart C x0 k x =
      affinePart k x + (C / 6) * ‖x - x0‖ ^ (3 : ℕ) := by
  rw [cubicNewtonEstimatingFunction, cubicallyRegularizedObjective_apply]
  ring

/-- Definition 4.2.14: a cubic-Newton estimating sequence for `f`, centered at `x0` with cubic
parameter `C` and Hessian-Lipschitz constant `L3`, consists of affine parts `ℓ_k`, points `x_k`,
scales `A_k`, and increments `a_k` such that
`ψ_k(x) = ℓ_k(x) + (C / 6) ‖x - x0‖^3`, each `x_k` minimizes `ψ_k`, the scales satisfy
`A_{k+1} = A_k + a_k`, and the recursive relations `𝓡_k^1` and `𝓡_k^2` hold. -/
structure CubicNewtonEstimatingSequence
    (f : E → ℝ) (x0 : E) (L3 C : ℝ) where
  /-- The affine parts `ℓ_k` of the estimating functions `ψ_k`. -/
  affinePart : ℕ → E →ᵃ[ℝ] ℝ
  /-- The minimizing points `x_k`. -/
  x : ℕ → E
  /-- The scaling parameters `A_k`. -/
  A : ℕ → ℝ
  /-- The increments `a_k` in the recursion `A_{k+1} = A_k + a_k`. -/
  a : ℕ → ℝ
  /-- The scaling parameters satisfy `A_{k+1} = A_k + a_k`. -/
  A_succ (k : ℕ) : A (k + 1) = A k + a k
  /-- Each point `x_k` globally minimizes the estimating function `ψ_k`. -/
  x_isMin (k : ℕ) :
    IsMinOn (cubicNewtonEstimatingFunction affinePart C x0 k) Set.univ (x k)
  /-- The recursive relation `𝓡_k^1`, written at the minimizing point `x_k` so that
  `ψ_k(x_k) = ψ_k^*`. -/
  value_lower (k : ℕ) :
    A k * f (x k) ≤ cubicNewtonEstimatingFunction affinePart C x0 k (x k)
  /-- The recursive relation `𝓡_k^2`: every estimating function is bounded above by
  `A_k f(x) + ((2 L₃ + C) / 6) ‖x - x0‖^3`. -/
  upper_bound (k : ℕ) (y : E) :
    cubicNewtonEstimatingFunction affinePart C x0 k y ≤
      A k * f y + ((2 * L3 + C) / 6) * ‖y - x0‖ ^ (3 : ℕ)

namespace CubicNewtonEstimatingSequence

variable {f : E → ℝ} {x0 : E} {L3 C : ℝ}

/-- A cubic-Newton estimating sequence can be used as its sequence of estimating functions
`ψ_k`. -/
instance :
    CoeFun (CubicNewtonEstimatingSequence f x0 L3 C) (fun _ ↦ ℕ → E → ℝ) where
  coe sequence := cubicNewtonEstimatingFunction sequence.affinePart C x0

/-- Evaluating a cubic-Newton estimating sequence at stage `k` recovers the textbook formula for
`ψ_k`. -/
@[simp] theorem apply
    (sequence : CubicNewtonEstimatingSequence f x0 L3 C) (k : ℕ) (y : E) :
    sequence k y =
      sequence.affinePart k y + (C / 6) * ‖y - x0‖ ^ (3 : ℕ) := by
  simpa using cubicNewtonEstimatingFunction_apply sequence.affinePart C x0 k y

/-- The distinguished point `x_k` globally minimizes the estimating function `ψ_k`. -/
theorem isMinOn
    (sequence : CubicNewtonEstimatingSequence f x0 L3 C) (k : ℕ) :
    IsMinOn (sequence k) Set.univ (sequence.x k) := by
  simpa using sequence.x_isMin k

/-- The lower recursive inequality `𝓡_k^1` written on the canonical estimating-function surface.
-/
theorem value_lower_apply
    (sequence : CubicNewtonEstimatingSequence f x0 L3 C) (k : ℕ) :
    sequence.A k * f (sequence.x k) ≤ sequence k (sequence.x k) := by
  simpa using sequence.value_lower k

/-- The upper recursive inequality `𝓡_k^2` written on the canonical estimating-function surface.
-/
theorem upper_bound_apply
    (sequence : CubicNewtonEstimatingSequence f x0 L3 C) (k : ℕ) (y : E) :
    sequence k y ≤
      sequence.A k * f y + ((2 * L3 + C) / 6) * ‖y - x0‖ ^ (3 : ℕ) := by
  simpa using sequence.upper_bound k y

end CubicNewtonEstimatingSequence

end
