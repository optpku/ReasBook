/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u}

/- Definition 5.4.9.7 lies in the Chapter 5 first-order calculus / sliced-derivative domain.

Sampled owner declarations:
- `gradient` in `Mathlib/Analysis/Calculus/Gradient/Basic`, the canonical owner for Euclidean
  gradients of scalar functions on a complete real inner-product space;
- `deriv` in `Mathlib/Analysis/Calculus/Deriv/Basic`, the canonical owner for one-variable
  derivatives;
- `gradient_eq_deriv'` in `Mathlib/Analysis/Calculus/Gradient/Basic`, the scalar bridge showing
  that the real gradient agrees with the ordinary derivative in one dimension;
- `secondOrderDerivativeBlock12` in `Definition_5_4_9_8`, the immediate downstream Chapter 5
  product-domain use of the same sliced `y`-gradient / `t`-derivative pattern.

Best owner abstraction:
- source-facing: the pointwise auxiliary slice derivatives `g₁(y, t)` and `g₂(y, t)`;
- core/canonical: mathlib's `gradient` on the frozen-`t` slice and `deriv` on the frozen-`y`
  slice;
- bridge/view: the pointwise pair `auxiliaryDerivatives f y t`.

Primitive data:
- the scalar-valued two-parameter function `f : E × ℝ → ℝ`.

Derived API:
- `auxiliaryGradient f y t`;
- `auxiliaryTimeDerivative f y t`;
- the pairing `auxiliaryDerivatives f y t`.

The previous version used a curried owner `f : E → ℝ → ℝ` and made the public bridge a pair of
functions. This refinement keeps the same mathematics but aligns the owner layer with the nearby
Chapter 5 product-domain calculus API: `f` lives on `E × ℝ`, the source-facing owners take the
explicit textbook binders `(y : E)` and `(t : ℝ)`, and the pair remains only as a thin bridge.
The ambient finite-dimensional `ℝⁿ` textbook model is still demoted to a specialization: only the
gradient owner needs mathlib's canonical completeness assumption, while
`auxiliaryTimeDerivative` lives directly at the sliced `deriv` level. -/

/-- The second auxiliary derivative `g₂(y,t)`, namely the derivative of the frozen-`y` slice of
`f`. -/
abbrev auxiliaryTimeDerivative (f : E × ℝ → ℝ) (y : E) (t : ℝ) : ℝ :=
  deriv (fun t' : ℝ ↦ f (y, t')) t

section Gradient

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The first auxiliary derivative `g₁(y,t)`, namely the gradient of the frozen-`t` slice of
`f`. -/
abbrev auxiliaryGradient (f : E × ℝ → ℝ) (y : E) (t : ℝ) : E :=
  ∇ (fun y' : E ↦ f (y', t)) y

/-- Definition 5.4.9.7: the auxiliary derivatives of `f(y,t)` are the pair whose first component
is the `y`-gradient and whose second component is the `t`-derivative. -/
abbrev auxiliaryDerivatives (f : E × ℝ → ℝ) (y : E) (t : ℝ) : E × ℝ :=
  (auxiliaryGradient f y t, auxiliaryTimeDerivative f y t)

/-- Expanding `auxiliaryDerivatives f y t` recovers the pair consisting of the frozen-`t`
gradient and the frozen-`y` time derivative. -/
theorem auxiliaryDerivatives_def (f : E × ℝ → ℝ) (y : E) (t : ℝ) :
    auxiliaryDerivatives f y t = (auxiliaryGradient f y t, auxiliaryTimeDerivative f y t) :=
  rfl

/-- The first component of `auxiliaryDerivatives f` is `auxiliaryGradient f`. -/
@[simp] theorem auxiliaryDerivatives_fst (f : E × ℝ → ℝ) (y : E) (t : ℝ) :
    (auxiliaryDerivatives f y t).1 = auxiliaryGradient f y t :=
  rfl

/-- The second component of `auxiliaryDerivatives f` is `auxiliaryTimeDerivative f`. -/
@[simp] theorem auxiliaryDerivatives_snd (f : E × ℝ → ℝ) (y : E) (t : ℝ) :
    (auxiliaryDerivatives f y t).2 = auxiliaryTimeDerivative f y t :=
  rfl

end Gradient
