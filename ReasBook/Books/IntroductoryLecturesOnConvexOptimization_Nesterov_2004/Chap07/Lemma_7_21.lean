/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Lemma 7.21 lies in the chapter's estimating-sequence recursion domain.

Sampled owner-style declarations:
* `IsEstimatingSequence` in `Chap02/Definition_2_21`, the chapter owner for affine upper models
  written via `AffineMap.lineMap`;
* `strongConvexEstimatingFunction_upper_bound_apply` in `Chap02/Lemma_2_8`, a stagewise
  estimating-function upper recursion theorem;
* `CubicNewtonEstimatingSequence` in `Chap04/Definition_4_2_14`, the chapter owner bundling
  `A`, `a`, and `ψ` when a full method object exists.

Source/core/bridge triage:
* source-facing: the additive recursion bound of Lemma 7.21 itself;
* core/canonical: the general estimating-sequence owner `IsEstimatingSequence`, which is nearby
  but not exact here because this lemma uses unnormalized accumulated weights `A_k` rather than an
  affine `lineMap` coefficient;
* bridge/view: none needed.

Primitive data:
* the set `Q`, transformed objective `hatF`, function family `ψ`, increments `a`, and accumulated
  weights `A`;
* the initial condition `A 0 = 0` and recursion `A (k + 1) = A k + a k`;
* the one-step upper bound for `ψ`.

Derived API:
* the global estimate `ψ k x ≤ A k * hatF x + ψ 0 x`.

Since no existing upstream owner theorem has this exact additive-recursion interface, this file
keeps the source-facing statement and only removes unnecessary `ℝ`-specificity.
-/

variable {X : Type u} {α : Type*} [Semiring α] [PartialOrder α] [IsOrderedRing α]

-- Proof sketch: argue by induction on `k`. The base case uses `A 0 = 0`. For the inductive step,
-- combine the one-step estimate `ψ (k + 1) x ≤ ψ k x + a k * hatF x` with the inductive
-- hypothesis and then rewrite the coefficient of `hatF x` using `A (k + 1) = A k + a k`.
/-- Lemma 7.21: if the estimating functions satisfy the one-step upper recursion
`ψ_{k+1}(x) ≤ ψ_k(x) + a_k \hat f(x)` on `Q`, with `A₀ = 0` and `A_{k+1} = A_k + a_k`, then
`ψ_k(x) ≤ A_k \hat f(x) + ψ_0(x)` for every `x ∈ Q`. This is the global estimating property
obtained from the nonlinear lower-support inequality used in the quasi-Newton method. -/
theorem estimating_function_le_weighted_transformed_objective_add_initial
    {Q : Set X} {hatF : X → α} {ψ : ℕ → X → α} {A a : ℕ → α}
    (hA0 : A 0 = 0)
    (hA_succ : ∀ k : ℕ, A (k + 1) = A k + a k)
    (hpsi_succ : ∀ k : ℕ, ∀ ⦃x : X⦄, x ∈ Q → ψ (k + 1) x ≤ ψ k x + a k * hatF x)
    (k : ℕ) (x : X) (hx : x ∈ Q) :
    ψ k x ≤ A k * hatF x + ψ 0 x := by
  induction k with
  | zero =>
      simp [hA0]
  | succ k ih =>
      calc
        ψ (k + 1) x ≤ ψ k x + a k * hatF x := hpsi_succ k hx
        _ ≤ (A k * hatF x + ψ 0 x) + a k * hatF x := add_le_add ih le_rfl
        _ = A k * hatF x + a k * hatF x + ψ 0 x := by ac_rfl
        _ = (A k + a k) * hatF x + ψ 0 x := by rw [← add_mul]
        _ = A (k + 1) * hatF x + ψ 0 x := by rw [hA_succ]
