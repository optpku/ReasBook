/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u}

/- Definition 4.1.5 lies in the regularized-Newton trajectory domain.

Sampled owner declarations:
* `Set.Ioc` in mathlib, the canonical owner for the admissible interval condition `M_k ∈ (0, 2L]`;
* `RegularizedNewton.acceptingParameters` in `Definition_4_1_16`, the later fixed-iterate
  acceptance owner that deliberately builds on top of, rather than inside, the weaker trajectory
  object defined here;
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the stronger Chapter 4 owner that adds
  accepted-step data and then forgets to the present relaxed iteration.

Source/core/bridge triage:
* source-facing: the relaxed trajectory data `x_k`, `M_k`, and `x_{k+1} = T_{M_k}(x_k)`;
* core/canonical: the iterate sequence, regularization sequence, and the interval owner
  `Set.Ioc 0 (2 * L)`;
* bridge/view: the coercion to the underlying trajectory `ℕ → X`.

Primitive data:
* the iterate sequence `x`;
* the regularization sequence `M_k`;
* the admissible-interval condition `M_k ∈ (0, 2L]`;
* the update law `x_{k+1} = T_{M_k}(x_k)`.

Derived API:
* the coercion to the iterate sequence;
* positivity of each `M_k`;
* the upper bound `M_k ≤ 2L`;
* positivity of `L`, derived from any admissible `M_k`.

The owner abstraction is therefore already the right one for this file: later chapter APIs add
acceptance or minimization data on top of this trajectory object, rather than replacing it by a
parallel wrapper. -/
/-- Definition 4.1.5: a relaxed regularized Newton iteration for a trial map `T_M` and constant
`L` consists of an iterate sequence `x_k` and regularization parameters `M_k` such that each
`M_k` lies in `(0, 2L]` and the update `x_{k+1} = T_{M_k}(x_k)` holds for every `k ≥ 0`. These
interval conditions force `L > 0`, recovered below as derived API. -/
structure RelaxedRegularizedNewtonIteration
    (stepMap : ℝ → X → X) (L : ℝ) where
  /-- The iterate sequence `x₀, x₁, x₂, ...`. -/
  x : ℕ → X
  /-- The regularization parameters `M₀, M₁, M₂, ...`. -/
  regularization : ℕ → ℝ
  /-- Every parameter `M_k` lies in the admissible interval `(0, 2L]`. -/
  regularization_mem_Ioc (k : ℕ) : regularization k ∈ Set.Ioc 0 (2 * L)
  /-- The next iterate is obtained by applying `T_{M_k}` to the current iterate `x_k`. -/
  x_succ (k : ℕ) : x (k + 1) = stepMap (regularization k) (x k)

namespace RelaxedRegularizedNewtonIteration

variable {stepMap : ℝ → X → X} {L : ℝ}

/-- A relaxed regularized Newton iteration can be used as its underlying iterate sequence `x_k`. -/
instance :
    CoeFun (RelaxedRegularizedNewtonIteration stepMap L) (fun _ ↦ ℕ → X) where
  coe method := method.x

/-- Every regularization parameter in a relaxed regularized Newton iteration is positive. -/
theorem regularization_pos
    (method : RelaxedRegularizedNewtonIteration stepMap L) (k : ℕ) :
    0 < method.regularization k :=
  (method.regularization_mem_Ioc k).1

/-- Every regularization parameter in a relaxed regularized Newton iteration is bounded above by
`2L`. -/
theorem regularization_le_two_mul_L
    (method : RelaxedRegularizedNewtonIteration stepMap L) (k : ℕ) :
    method.regularization k ≤ 2 * L :=
  (method.regularization_mem_Ioc k).2

/-- The regularization scale `L` is positive. -/
theorem L_pos
    (method : RelaxedRegularizedNewtonIteration stepMap L) :
    0 < L := by
  have h0 : 0 < method.regularization 0 :=
    method.regularization_pos 0
  have hL : method.regularization 0 ≤ 2 * L :=
    method.regularization_le_two_mul_L 0
  linarith

end RelaxedRegularizedNewtonIteration
