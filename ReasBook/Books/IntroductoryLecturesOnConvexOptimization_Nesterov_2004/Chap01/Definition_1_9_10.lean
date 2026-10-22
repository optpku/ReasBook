/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_9_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient

noncomputable section

namespace NonlinearConjugateGradientMethod

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 1.9.10 is `source-facing`: it names the standard nonlinear conjugate-gradient
coefficient sequences in terms of the objective `f`, the iterate sequence `xₖ`, and the search
directions `pₖ`.

Source/core/bridge triage:
* source-facing: the Dai--Yuan, Fletcher--Reeves, and Polak--Ribiere coefficient sequences on
  `(f, x, p)`
* core/canonical: the surrounding recursive owners
  `nonlinearConjugateGradientIterates`, `nonlinearConjugateGradientDirections`, the method owner
  `_root_.NonlinearConjugateGradientMethod`, and the line-search owner
  `SatisfiesExactLineSearchAlong`
* bridge/view: the pointwise evaluation lemmas below

Primary domain:
* nonlinear conjugate-gradient coefficient formulas on a real inner product space

Sampled owner-style declarations:
* `nonlinearConjugateGradientIterates`
* `nonlinearConjugateGradientDirections`
* `_root_.NonlinearConjugateGradientMethod`
* `SatisfiesExactLineSearchAlong`

There is no upstream owner that already defines these three textbook coefficient formulas, so the
primitive public data here remain exactly the source-level triple `(f, x, p)`.
-/

section

variable (f : E → ℝ) (x p : ℕ → E)

/-- Definition 1.9.10 (1): the Dai--Yuan nonlinear conjugate-gradient coefficient sequence is
given by
`βₖ = ‖∇f(xₖ₊₁)‖² / ⟪∇f(xₖ₊₁) - ∇f(xₖ), pₖ⟫`. -/
def daiYuanBeta : ℕ → ℝ :=
  fun k ↦
    ‖∇ f (x (k + 1))‖ ^ 2 / inner ℝ (∇ f (x (k + 1)) - ∇ f (x k)) (p k)

/-- Evaluating the Dai--Yuan coefficient sequence at index `k` recovers the textbook formula. -/
@[simp] theorem daiYuanBeta_apply (k : ℕ) :
    daiYuanBeta f x p k =
      ‖∇ f (x (k + 1))‖ ^ 2 / inner ℝ (∇ f (x (k + 1)) - ∇ f (x k)) (p k) :=
  rfl

/-- Definition 1.9.10 (2): the Fletcher--Reeves nonlinear conjugate-gradient coefficient sequence
is given by `βₖ = ‖∇f(xₖ₊₁)‖² / ‖∇f(xₖ)‖²`. -/
def fletcherReevesBeta : ℕ → ℝ :=
  fun k ↦ ‖∇ f (x (k + 1))‖ ^ 2 / ‖∇ f (x k)‖ ^ 2

/-- Evaluating the Fletcher--Reeves coefficient sequence at index `k` recovers the textbook
formula. -/
@[simp] theorem fletcherReevesBeta_apply (k : ℕ) :
    fletcherReevesBeta f x k =
      ‖∇ f (x (k + 1))‖ ^ 2 / ‖∇ f (x k)‖ ^ 2 :=
  rfl

/-- Definition 1.9.10 (3): the Polak--Ribiere nonlinear conjugate-gradient coefficient sequence is
given by
`βₖ = ⟪∇f(xₖ₊₁), ∇f(xₖ₊₁) - ∇f(xₖ)⟫ / ‖∇f(xₖ)‖²`. -/
def polakRibiereBeta : ℕ → ℝ :=
  fun k ↦
    inner ℝ (∇ f (x (k + 1))) (∇ f (x (k + 1)) - ∇ f (x k)) / ‖∇ f (x k)‖ ^ 2

/-- Evaluating the Polak--Ribiere coefficient sequence at index `k` recovers the textbook
formula. -/
@[simp] theorem polakRibiereBeta_apply (k : ℕ) :
    polakRibiereBeta f x k =
      inner ℝ (∇ f (x (k + 1))) (∇ f (x (k + 1)) - ∇ f (x k)) / ‖∇ f (x k)‖ ^ 2 :=
  rfl

end

end NonlinearConjugateGradientMethod

end
